// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0
//
//! PRISM v2 — Polyglot Resolution via Inverted Symbol Map, version 2.
//!
//! v2 is a *scope-aware* call-graph resolver. Compared with v1, it trades a
//! small amount of extra bookkeeping for a large gain in precision:
//!
//!   * v1 resolves an unresolved short name with a single global
//!     "first definition wins" lookup. That is fast but wrong whenever two
//!     unrelated symbols share a short name (`__init__`, `run`, `handle`,
//!     `Get`...), which is the common case in real repos.
//!
//!   * v2 resolves the same short name through a *scope ladder*:
//!     explicit import  →  same file  →  same package/dir  →  project-wide
//!     Imports are resolved to files: Python `from m import f [as g]`,
//!     `import a.b [as c]`, relative `from .m import f`; JS/TS named,
//!     default and namespace imports from relative paths and from the `@/`
//!     alias (resolved inside the importing file's own app), following
//!     re-exports (`__init__.py`, barrel `index.ts`) a few hops deep.
//!     Only if the caller is still unresolved at every tighter tier does it
//!     fall back to the loose global search, and even then it refuses
//!     names that are too common (`max_ambiguous`).
//!
//!   * Every call edge records *how* it was resolved (`resolution`):
//!     `import` / `local` / `package` are tied to the caller's code;
//!     `name` is a by-name guess with a single candidate in the project;
//!     `ambiguous` is a by-name guess with several candidates — the caller
//!     then gets one `ambiguous` edge per candidate instead of a silently
//!     picked one, and queries show them apart from the exact callers.
//!
//! v2 also understands class hierarchies: `self.foo()` and
//! `BaseClass.foo()` can be resolved through the inheritance chain rather
//! than a name-only guess.
//!
//! On a ~64k-file polyglot repo this runs in ~1.4s with ~3.1GB peak RSS,
//! producing ~773k nodes and ~1.5M edges. That is the target profile.

use crate::struc::kb_struct::{
    CallGraph, CallGraphEdge, CallGraphNode, CallerInfo, FileData, KnowledgeBase, Parameter,
};
use rayon::prelude::*;
use std::borrow::Cow;
use std::cmp::Reverse;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::collections::VecDeque;

type Map<K, V> = HashMap<K, V>;

const ENTRY_TAG: &str = "entry-point";
/// Prefixes the parser adds to synthesized IDs (`func_foo`, `method_Bar.baz`).
/// Stripping them is what lets us compare against a caller's raw name.
const KNOWN_PREFIXES: [&str; 4] = ["func_", "method_", "class_", "struct_"];
/// Spellings of the implicit receiver across the languages we support.
const SELF_NAMES: [&str; 6] = ["self", "this", "cls", "_self", "self_", "myself"];
/// Cap on the BFS depth when walking the class hierarchy. Real hierarchies
/// are shallow; a cap here prevents a cyclic or adversarial graph from
/// blowing up the walk.
const MAX_CHAIN: usize = 64;
const EDGE_CALL: u8 = 0;
const EDGE_INHERIT: u8 = 1;
/// How many re-export hops (`__init__.py`, barrel `index.ts`) an import is
/// followed through before giving up.
const MAX_REEXPORT: u8 = 3;

/// How a call edge was resolved. Lower = tighter; when one caller reaches
/// the same target twice, the tighter resolution is kept.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Via {
    Import = 0,
    Local = 1,
    Package = 2,
    Name = 3,
    Ambiguous = 4,
}

impl Via {
    fn as_str(self) -> &'static str {
        match self {
            Via::Import => "import",
            Via::Local => "local",
            Via::Package => "package",
            Via::Name => "name",
            Via::Ambiguous => "ambiguous",
        }
    }
}

/// Result of resolving one reference.
enum Hit {
    One(u32, Via),
    /// Several equally good by-name candidates, best guess first.
    Many(Vec<u32>),
}

impl Hit {
    /// The single best guess (for inheritance, class qualifiers).
    fn best(&self) -> u32 {
        match self {
            Hit::One(i, _) => *i,
            Hit::Many(v) => v[0],
        }
    }
}

#[derive(Clone, Debug)]
pub struct CallGraphOptions {
    /// A bare name that matches more than this many project symbols (and could
    /// not be pinned down by file / import / package) is considered too generic
    /// (`Get`, `Close`, `String`...) and produces no edge.
    pub max_ambiguous: usize,
    /// If a name or qualifier comes from an import that does not map to a file
    /// in the project (stdlib, third-party), never fall back to a global name
    /// search. Turn off if your TS code uses path aliases (`@app/...`) that
    /// the module index cannot resolve.
    pub strict_imports: bool,
}

impl Default for CallGraphOptions {
    fn default() -> Self {
        Self {
            max_ambiguous: 8,
            strict_imports: true,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Function,
    Method,
    Class,
}

/// What the call site *looks like* syntactically. This is what the resolver
/// uses to decide which kinds of targets are acceptable.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Want {
    /// `foo()`
    Call,
    /// `x.foo()` where x is an unknown receiver
    MethodCall,
    /// base class / static receiver
    Class,
}

/// Borrowed view of everything the resolver needs about one node.
/// All `&'a str` fields point into the original `KnowledgeBase`, so the
/// resolver allocates essentially nothing per node.
struct Node<'a> {
    id: &'a str,
    name: &'a str,
    kind: Kind,
    file: u32,
    is_entry: bool,
    owner: Option<&'a str>,
}

#[derive(Clone, Copy)]
struct RawEdge {
    from: u32,
    to: u32,
    line: u32,
    kind: u8,
    conditional: bool,
    via: Via,
}

struct BaseRef<'a> {
    class: &'a str,
    base: &'a str,
    file: u32,
    line: u32,
}

/// `None` = the module is not part of the project (stdlib / third party).
/// `Some(files)` = this import/namespace resolves to those file indices.
type Target<'a> = Option<&'a [u32]>;

#[derive(Default)]
struct FileImports<'a> {
    /// `import { foo } from "x"` — `foo` may be called bare as `foo()`.
    /// Value: where it comes from, and its name *there* (`import { a as b }`
    /// binds `b`, but the definition is called `a`).
    names: Map<&'a str, (Target<'a>, &'a str)>,
    /// `import * as ns from "x"` or `import x.y` — `ns.foo()` / `x.y.foo()`.
    namespaces: Map<&'a str, Target<'a>>,
    /// `from m import *` / `export * from "m"` — everything re-exported.
    star: Vec<&'a [u32]>,
}

/// Everything a single parallel chunk extracts from its slice of files.
struct Extract<'a> {
    nodes: Vec<Node<'a>>,
    bases: Vec<BaseRef<'a>>,
    imports: Vec<FileImports<'a>>,
}

// ───────────────────────────── string helpers ─────────────────────────────

#[inline]
fn sep(c: char) -> bool {
    c == '.' || c == ':' || c == '/'
}

#[inline]
fn clean_path(p: &str) -> &str {
    p.trim_start_matches("./")
}

#[inline]
fn dir_of(p: &str) -> &str {
    clean_path(p).rsplit_once('/').map_or("", |(d, _)| d)
}

/// `func_newFileCache::eulix-cli/internal/x.go` -> `newFileCache`
/// `method_Cache.Get::a/b.go` / `func_Foo::bar::a/b.go` -> `Get` / `bar`
///
/// This is the "short name" we index by. It deliberately strips:
///   * the `func_` / `method_` / `class_` / `struct_` prefix
///   * everything after the last `::` (the file/scope suffix)
///   * a trailing `.name` segment (dotted qualifier)
#[inline]
fn bare_name(id: &str) -> &str {
    let name = id.rsplit_once("::").map_or(id, |(n, _)| n);
    let name = KNOWN_PREFIXES
        .iter()
        .find_map(|p| name.strip_prefix(p))
        .unwrap_or(name);
    let name = name.rsplit("::").next().unwrap_or(name);
    name.rsplit('.').next().unwrap_or(name)
}

/// `a.b.c` -> (Some("a.b"), "c");  `Foo::bar` -> (Some("Foo"), "bar")
///
/// The two separators overlap (`::` contains `:`), so we compare the last
/// index of each and take whichever is further right — that's the actual
/// last separator in the string.
#[inline]
fn split_callee(c: &str) -> (Option<&str>, &str) {
    match (c.rfind('.'), c.rfind("::")) {
        (None, None) => (None, c),
        (Some(d), None) => (Some(&c[..d]), &c[d + 1..]),
        (None, Some(p)) => (Some(&c[..p]), &c[p + 2..]),
        (Some(d), Some(p)) => {
            if d > p {
                (Some(&c[..d]), &c[d + 1..])
            } else {
                (Some(&c[..p]), &c[p + 2..])
            }
        }
    }
}

#[inline]
fn first_self_param(params: &[Parameter]) -> bool {
    params
        .first()
        .map(|p| SELF_NAMES.contains(&p.name.as_str()))
        .unwrap_or(false)
}

#[inline]
fn is_self_qualifier(q: &str) -> bool {
    SELF_NAMES.contains(&q) || q == "Self" || q == "super"
}

/// Name a node is indexed by: the parser's own `name` (last dotted / `::`
/// segment), falling back to the id. The id alone is not enough: Python and
/// JS/TS method ids are `method_<Class>_<name>`, so `bare_name` would give
/// `Class_name` and no `self.name()` call could ever reach the method.
fn node_name<'a>(name: &'a str, id: &'a str) -> &'a str {
    let n = name.rsplit("::").next().unwrap_or(name);
    let n = n.rsplit('.').next().unwrap_or(n).trim();
    if n.is_empty() {
        bare_name(id)
    } else {
        n
    }
}

/// Number of leading path components `a` and `b` share (byte-aligned to `/`).
/// Used as a cheap "closeness" heuristic: a candidate in a nearby directory
/// is a better guess than one on the other side of the tree.
/// Language family of a file, from `FileData.language`. A name can only
/// resolve to a symbol of the same family: in a polyglot repo a TypeScript
/// `list.find()` must not land on a Python `def find`. 0 = unknown, which
/// matches anything (keeps hand-built test fixtures and new languages
/// working).
fn language_family(language: &str) -> u8 {
    match language {
        "python" => 1,
        "typescript" | "javascript" | "tsx" | "jsx" => 2,
        "go" => 3,
        "rust" => 4,
        "java" => 5,
        "c" | "cpp" => 6,
        _ => 0,
    }
}

fn common_dir_prefix(a: &str, b: &str) -> usize {
    let (a, b) = (clean_path(a).as_bytes(), clean_path(b).as_bytes());
    let (mut last_slash, mut i) = (0, 0);
    while i < a.len().min(b.len()) && a[i] == b[i] {
        if a[i] == b'/' {
            last_slash = i + 1;
        }
        i += 1;
    }
    last_slash
}

// module index
//
// Maps every component-suffix of every file stem AND every directory to the
// files it denotes. Keys are borrowed slices of the file paths (no allocation).
//   src/a/b.py   -> "src/a/b", "a/b", "b"      (python / rust / js module)
//   pkg/retr/x.go-> "pkg/retr", "retr"         (go package = directory)
//
// The suffix trick is what makes the index polyglot: every language's module
// syntax is expressible as some suffix of a path, so we can look up "retr"
// and match `pkg/retr/x.go` without knowing we're in Go.
fn add_suffixes<'a>(map: &mut Map<&'a str, Vec<u32>>, s: &'a str, file: u32) {
    let mut cur = s;
    while !cur.is_empty() {
        let v = map.entry(cur).or_default();
        if v.last() != Some(&file) {
            v.push(file);
        }
        match cur.split_once('/') {
            Some((_, rest)) => cur = rest,
            None => break,
        }
    }
}

struct ModuleIndex<'a> {
    /// Every component-suffix of every stem and directory (see above).
    suffix: Map<&'a str, Vec<u32>>,
    /// Full file stem only (`apps/web/src/lib/x`) — exact path lookups for
    /// relative imports, where a suffix match would be a guess.
    stems: Map<&'a str, Vec<u32>>,
}

fn build_module_index<'a>(files: &[&'a str]) -> ModuleIndex<'a> {
    let mut map: Map<&'a str, Vec<u32>> = Map::with_capacity(files.len() * 3);
    let mut stems: Map<&'a str, Vec<u32>> = Map::with_capacity(files.len());
    for (i, &path) in files.iter().enumerate() {
        let cleaned = clean_path(path);
        // File "stem": drop the extension, but only if the last `.` is not
        // part of a directory name (a common gotcha on paths like `v1.2/x`).
        let stem = match cleaned.rfind('.') {
            Some(d) if !cleaned[d..].contains('/') => &cleaned[..d],
            _ => cleaned,
        };
        add_suffixes(&mut map, stem, i as u32);
        stems.entry(stem).or_default().push(i as u32);
        if let Some(slash) = stem.rfind('/') {
            add_suffixes(&mut map, &stem[..slash], i as u32);
        }
    }
    ModuleIndex { suffix: map, stems }
}

/// Exact project path (no extension) -> files: the module file itself, else
/// the package's `index` / `__init__`, else every file of that directory.
fn resolve_path<'a>(p: &str, index: &'a ModuleIndex<'a>) -> Target<'a> {
    if p.is_empty() {
        return None;
    }
    if let Some(v) = index.stems.get(p) {
        return Some(v.as_slice());
    }
    for tail in ["index", "__init__"] {
        if let Some(v) = index.stems.get(format!("{p}/{tail}").as_str()) {
            return Some(v.as_slice());
        }
    }
    index.suffix.get(p).map(Vec::as_slice)
}

/// `a/b/../c/./d` -> `a/c/d`; `None` if `..` climbs above the root.
fn normalize(p: &str) -> Option<String> {
    let mut out: Vec<&str> = Vec::new();
    for part in p.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                out.pop()?;
            }
            _ => out.push(part),
        }
    }
    Some(out.join("/"))
}

/// Python `..pkg.mod` imported from `a/b/c.py` -> `a/pkg/mod`.
fn python_relative(file: &str, module: &str) -> Option<String> {
    let dots = module.bytes().take_while(|&b| b == b'.').count();
    let rest = &module[dots..];
    let mut base: Vec<&str> = dir_of(file).split('/').filter(|s| !s.is_empty()).collect();
    for _ in 1..dots {
        base.pop()?;
    }
    base.extend(rest.split('.').filter(|s| !s.is_empty()));
    Some(base.join("/"))
}

/// `./x`, `../y/z.js` relative to the importing file, extension dropped.
fn js_relative(file: &str, module: &str) -> Option<String> {
    let m = strip_js_ext(module);
    normalize(&format!("{}/{}", dir_of(file), m))
}

fn strip_js_ext(m: &str) -> &str {
    for ext in [".tsx", ".ts", ".jsx", ".js", ".mjs", ".cjs"] {
        if let Some(r) = m.strip_suffix(ext) {
            return r;
        }
    }
    m
}

/// `@/lib/x` (or `~/lib/x`) from `apps/web/src/app/page.tsx`: the alias
/// points into the importing file's *own* app, so look for `<ancestor>/src/
/// lib/x` from the nearest ancestor up — never into a sibling app. This is
/// the `"@/*": ["./src/*"]` convention (Next.js, Expo); tsconfig `paths`
/// themselves are not read.
fn js_alias<'a>(file: &str, rest: &str, index: &'a ModuleIndex<'a>) -> Target<'a> {
    let rest = strip_js_ext(rest);
    let mut dir = dir_of(file);
    loop {
        let cand = if dir.is_empty() {
            format!("src/{rest}")
        } else {
            format!("{dir}/src/{rest}")
        };
        if let Some(t) = normalize(&cand).and_then(|c| resolve_path(&c, index)) {
            return Some(t);
        }
        if dir.is_empty() {
            return None;
        }
        dir = dir.rsplit_once('/').map_or("", |(d, _)| d);
    }
}

fn resolve_module<'a>(module: &str, index: &'a ModuleIndex<'a>) -> Target<'a> {
    let index = &index.suffix;
    let mut m = module.trim().trim_start_matches(['.', '/']);
    // Peel common alias prefixes until none match.
    for p in ["@/", "~/", "crate::", "self::", "super::"] {
        while let Some(r) = m.strip_prefix(p) {
            m = r;
        }
    }
    if m.is_empty() {
        return None;
    }
    // Dotted / `::`-separated modules (python, rust, java) become path-like.
    let norm: Cow<str> = if !m.contains('/') && (m.contains('.') || m.contains("::")) {
        Cow::Owned(m.replace("::", "/").replace('.', "/"))
    } else {
        Cow::Borrowed(m)
    };
    // `github.com/acme/proj/internal/x` must match dir `proj/internal/x` or
    // `internal/x`, but never a lone `x`, otherwise `context`, `errors`, ...
    // would match random project folders.
    let min_parts = norm.split('/').count().min(2);
    let mut cur: &str = &norm;
    loop {
        if let Some(v) = index.get(cur) {
            return Some(v.as_slice());
        }
        let (_, rest) = cur.split_once('/')?;
        if rest.split('/').count() < min_parts {
            return None;
        }
        cur = rest;
    }
}

fn build_file_imports<'a>(
    fd: &'a FileData,
    path: &str,
    index: &'a ModuleIndex<'a>,
) -> FileImports<'a> {
    match language_family(&fd.language) {
        1 => python_imports(fd, path, index),
        2 => js_imports(fd, path, index),
        _ => generic_imports(fd, index),
    }
}

/// Exported name of a local import binding (`as` renames).
fn exported_of<'a>(imp: &'a crate::struc::kb_struct::Import, local: &'a str) -> &'a str {
    imp.renamed
        .iter()
        .find(|(l, _)| l == local)
        .map_or(local, |(_, e)| e.as_str())
}

fn python_imports<'a>(fd: &'a FileData, path: &str, index: &'a ModuleIndex<'a>) -> FileImports<'a> {
    let mut out = FileImports::default();
    for imp in &fd.imports {
        let module = imp.module.trim();
        let relative = module.starts_with('.');
        // Module path as a project path: `a.b.c` -> `a/b/c` (suffix-matched,
        // which covers src-layout packages: `packages/x/src/a/b/c.py`), or
        // `..a` -> an exact path next to the importing file.
        let target = if relative {
            python_relative(path, module).and_then(|p| resolve_path(&p, index))
        } else {
            resolve_module(module, index)
        };
        let submodule = |item: &str| -> Target<'a> {
            if relative {
                python_relative(path, module)
                    .and_then(|p| normalize(&format!("{p}/{item}")))
                    .and_then(|p| index.stems.get(p.as_str()).map(Vec::as_slice))
            } else {
                resolve_module(&format!("{module}.{item}"), index).filter(|_| !module.is_empty())
            }
        };
        for item in &imp.items {
            if item == "*" {
                if let Some(fs) = target {
                    out.star.push(fs);
                }
                continue;
            }
            let exported = exported_of(imp, item);
            out.names.entry(item.as_str()).or_insert((target, exported));
            // `from pkg import mod` + `mod.f()`: the item may be a module.
            let ns = submodule(exported).or(target);
            out.namespaces.entry(item.as_str()).or_insert(ns);
        }
        if imp.items.is_empty() {
            // `import a.b.c` binds `a`; `import a.b.c as m` binds `m`.
            let local = match imp.alias.as_deref() {
                Some(a) => a,
                None => module.split('.').next().unwrap_or(module),
            };
            if !local.is_empty() {
                out.namespaces.entry(local).or_insert(target);
            }
        }
    }
    out
}

fn js_imports<'a>(fd: &'a FileData, path: &str, index: &'a ModuleIndex<'a>) -> FileImports<'a> {
    let mut out = FileImports::default();
    for imp in &fd.imports {
        let m = imp.module.trim();
        let target = if m.starts_with("./") || m.starts_with("../") || m == "." || m == ".." {
            js_relative(path, m).and_then(|p| resolve_path(&p, index))
        } else if let Some(rest) = m.strip_prefix("@/").or_else(|| m.strip_prefix("~/")) {
            js_alias(path, rest, index)
        } else {
            // Bare specifier: a package. A workspace package may still map
            // to project files by suffix; otherwise it is external.
            resolve_module(m, index)
        };
        for item in &imp.items {
            if item == "*" {
                if let Some(fs) = target {
                    out.star.push(fs);
                }
                continue;
            }
            let exported = exported_of(imp, item);
            out.names.entry(item.as_str()).or_insert((target, exported));
            // A default or namespace import can head a call: `api.get()`.
            out.namespaces.entry(item.as_str()).or_insert(target);
        }
        if let Some(a) = imp.alias.as_deref() {
            out.namespaces.entry(a).or_insert(target);
        }
    }
    out
}

/// Go, Rust, Java, C/C++: the historical, module-suffix based behaviour.
fn generic_imports<'a>(fd: &'a FileData, index: &'a ModuleIndex<'a>) -> FileImports<'a> {
    let mut out = FileImports::default();
    for imp in &fd.imports {
        let target = resolve_module(&imp.module, index);
        for item in &imp.items {
            // A named import can appear either as a bare call (`foo()`) or
            // as the head of a qualified call (`foo.bar()`), so we register
            // it in both maps. `or_insert` keeps the first registration, so
            // a name imported twice does not flip-flop.
            out.names
                .entry(item.as_str())
                .or_insert((target, exported_of(imp, item)));
            out.namespaces.entry(item.as_str()).or_insert(target);
        }
        if let Some(a) = imp.alias.as_deref() {
            out.namespaces.entry(a).or_insert(target);
        }
        // `import "a/b/retrieval"` -> `retrieval.X()`;  `import a.b.c` -> `a.b.c.X()`
        let m = imp.module.trim_end_matches('/');
        if let Some(last) = m.rsplit(sep).find(|s| !s.is_empty()) {
            out.namespaces.entry(last).or_insert(target);
        }
        if !m.contains('/') {
            if let Some(first) = m.split(sep).find(|s| !s.is_empty()) {
                out.namespaces.entry(first).or_insert(target);
            }
        }
    }
    out
}

/// Collapse the edges of ONE caller: one edge per target, first call-site line,
/// `conditional` only if *every* call to that target is conditional.
///
/// This is deliberately per-caller (not global): it keeps the graph from
/// growing with the number of call sites inside the same function, which
/// matters a lot on machine-generated code.
fn flush_edges(out: &mut Vec<RawEdge>, buf: &mut Vec<RawEdge>) {
    buf.sort_unstable_by_key(|e| (e.to, e.line));
    let mut it = buf.drain(..);
    if let Some(mut cur) = it.next() {
        for e in it {
            if e.to == cur.to {
                cur.conditional &= e.conditional;
                cur.via = cur.via.min(e.via);
            } else {
                out.push(cur);
                cur = e;
            }
        }
        out.push(cur);
    }
}

/// Rank how well a candidate of kind `k` fits a call site of shape `want`.
/// Lower is better. `None` means "this candidate cannot satisfy the call
/// site at all" and is dropped.
fn rank(want: Want, k: Kind, strict: bool) -> Option<u8> {
    use Kind::*;
    match (want, k) {
        (Want::Class, Class) => Some(0),
        (Want::Class, _) => None,
        (Want::Call, Function) => Some(0),
        (Want::Call, Class) => Some(1),
        (Want::Call, Method) => (!strict).then_some(2),
        (Want::MethodCall, Method) => Some(0),
        (Want::MethodCall, Function) => Some(1),
        (Want::MethodCall, Class) => Some(2),
    }
}

/// `rank`, plus what the caller's language rules out. In Python and JS/TS
/// (`family` 1 / 2) a receiver call `x.f()` only ever reaches a method — a
/// function or class of another module is reached through an import, which
/// the namespace tier already handled — and a bare `f()` never reaches a
/// method (that needs `self.` / `this.`). Without this, every
/// `session.execute()` became a call to some project `def execute`.
fn rank_in(family: u8, want: Want, k: Kind, strict: bool) -> Option<u8> {
    if family == 1 || family == 2 {
        match (want, k) {
            (Want::MethodCall, Kind::Function | Kind::Class) => return None,
            (Want::Call, Kind::Method) => return None,
            _ => {}
        }
    }
    rank(want, k, strict)
}

struct Resolver<'a> {
    nodes: &'a [Node<'a>],
    node_map: &'a Map<&'a str, u32>,
    /// bare name -> node indices, ascending (=> also ascending by file).
    by_name: &'a Map<&'a str, Vec<u32>>,
    files: &'a [&'a str],
    /// file idx -> dir id; non-decreasing because files are sorted by (dir, path)
    file_dir: &'a [u32],
    /// file idx -> language family (see `language_family`)
    file_family: &'a [u8],
    imports: &'a [FileImports<'a>],
    /// (class idx, method name, method idx), sorted — enables binary search
    /// for "does this class define this method".
    methods: &'a [(u32, &'a str, u32)],
    parents: Map<u32, Vec<u32>>,
    children: Map<u32, Vec<u32>>,
    max_ambiguous: usize,
    strict_imports: bool,
}

impl<'a> Resolver<'a> {
    /// Best candidate + how many were eligible to be picked.
    ///
    /// `closeness` is off in tiers where the candidate set is already
    /// constrained (same file, same package) — the tie-break would just be
    /// noise and costs a byte-scan per candidate.
    fn pick(
        &self,
        cands: impl Iterator<Item = u32>,
        want: Want,
        strict: bool,
        file: u32,
        closeness: bool,
    ) -> (Option<u32>, usize) {
        let mut best: Option<(u8, Reverse<usize>, u32)> = None;
        let mut eligible = 0usize;
        let fam = self.file_family[file as usize];
        for c in cands {
            let n = &self.nodes[c as usize];
            let cfam = self.file_family[n.file as usize];
            if fam != 0 && cfam != 0 && fam != cfam {
                continue;
            }
            let Some(r) = rank_in(fam, want, n.kind, strict) else {
                continue;
            };
            eligible += 1;
            let close = if closeness {
                common_dir_prefix(self.files[file as usize], self.files[n.file as usize])
            } else {
                0
            };
            // Sort by (rank, close desc, idx asc) — the last term keeps the
            // result deterministic when rank and closeness tie.
            let key = (r, Reverse(close), c);
            if best.is_none_or(|b| key < b) {
                best = Some(key);
            }
        }
        (best.map(|k| k.2), eligible)
    }

    /// Restrict a name lookup to files belonging to a resolved import.
    /// `fs` is sorted, so the inner filter is a binary search per candidate.
    /// If those files do not define `name` but re-export it (`__init__.py`
    /// doing `from .x import name`, a barrel `export { name } from "./x"`,
    /// `export *`), follow the re-export, at most `MAX_REEXPORT` hops.
    fn lookup_in_files(
        &self,
        name: &str,
        fs: &[u32],
        file: u32,
        want: Want,
        depth: u8,
    ) -> Option<u32> {
        if let Some(cands) = self.by_name.get(name) {
            let it = cands
                .iter()
                .copied()
                .filter(|&c| fs.binary_search(&self.nodes[c as usize].file).is_ok());
            if let (Some(x), _) = self.pick(it, want, false, file, true) {
                return Some(x);
            }
        }
        if depth >= MAX_REEXPORT {
            return None;
        }
        for &f in fs {
            let imp = &self.imports[f as usize];
            if let Some(&(Some(next), exported)) = imp.names.get(name) {
                if let Some(x) = self.lookup_in_files(exported, next, file, want, depth + 1) {
                    return Some(x);
                }
            }
            for next in &imp.star {
                if let Some(x) = self.lookup_in_files(name, next, file, want, depth + 1) {
                    return Some(x);
                }
            }
        }
        None
    }

    /// Scope ladder; the first tier that yields a candidate wins:
    /// explicit import -> same file -> same package/dir -> project-wide.
    ///
    /// `by_name[name]` is globally sorted by file idx, and file idx is
    /// itself sorted by (dir, path). That lets each tier slice the candidate
    /// list with `partition_point` instead of filtering the whole thing.
    fn lookup(&self, name: &str, file: u32, want: Want) -> Option<Hit> {
        // Tier 1: explicit import. `(None, _)` means the import resolved
        // to a module outside the project — under `strict_imports` we refuse
        // to fall through, since that would just be guessing. A receiver
        // call (`x.name()`) is not the imported `name`, so it skips this.
        if want != Want::MethodCall {
            let imp = &self.imports[file as usize];
            match imp.names.get(name) {
                Some(&(Some(fs), exported)) => {
                    if let Some(x) = self.lookup_in_files(exported, fs, file, want, 0) {
                        return Some(Hit::One(x, Via::Import));
                    }
                }
                Some((None, _)) if self.strict_imports => return None,
                _ => {}
            }
            // `from m import *` / `export * from "m"` in the caller's file.
            for fs in &imp.star {
                if let Some(x) = self.lookup_in_files(name, fs, file, want, 0) {
                    return Some(Hit::One(x, Via::Import));
                }
            }
        }

        let cands = self.by_name.get(name)?.as_slice();
        let fam = self.file_family[file as usize];

        // Tier 2: same file.
        let lo = cands.partition_point(|&c| self.nodes[c as usize].file < file);
        let hi = lo + cands[lo..].partition_point(|&c| self.nodes[c as usize].file <= file);
        if let (Some(x), _) = self.pick(cands[lo..hi].iter().copied(), want, false, file, false) {
            return Some(Hit::One(x, Via::Local));
        }

        // Tier 3: same package/dir. Same partition_point trick, on dir id.
        let d = self.file_dir[file as usize];
        let dir_of_c = |c: u32| self.file_dir[self.nodes[c as usize].file as usize];
        let lo = cands.partition_point(|&c| dir_of_c(c) < d);
        let hi = lo + cands[lo..].partition_point(|&c| dir_of_c(c) <= d);
        if fam == 1 || fam == 2 {
            // Python and JS/TS have no package scope: a sibling module's
            // name is visible only through an import, so a hit here is a
            // by-name guess, and is labelled as one — and, like any by-name
            // guess, refused for a name too generic to mean anything
            // (`x.get()` with a dozen `get` methods in the project).
            let (_, eligible) = self.pick(cands.iter().copied(), want, true, file, false);
            if eligible > self.max_ambiguous.max(1) {
                return None;
            }
            if let Some(hit) = self.by_name_only(&cands[lo..hi], file, want, false) {
                return Some(hit);
            }
        } else if let (Some(x), _) =
            self.pick(cands[lo..hi].iter().copied(), want, false, file, false)
        {
            return Some(Hit::One(x, Via::Package));
        }

        // Tier 4: project-wide, by name only, and only if the name is not
        // too generic.
        let (_, eligible) = self.pick(cands.iter().copied(), want, true, file, false);
        if eligible > self.max_ambiguous.max(1) {
            return None;
        }
        self.by_name_only(cands, file, want, true)
    }

    /// A by-name match among `cands`: the one best-ranked candidate -> a
    /// `name` hit; several -> all of them (`ambiguous`), closest first.
    /// Never a silent pick between equals.
    fn by_name_only(&self, cands: &[u32], file: u32, want: Want, strict: bool) -> Option<Hit> {
        let fam = self.file_family[file as usize];
        let mut best_rank = u8::MAX;
        let mut top: Vec<u32> = Vec::new();
        for &c in cands {
            let n = &self.nodes[c as usize];
            let cfam = self.file_family[n.file as usize];
            if fam != 0 && cfam != 0 && fam != cfam {
                continue;
            }
            let Some(r) = rank_in(fam, want, n.kind, strict) else {
                continue;
            };
            if r < best_rank {
                best_rank = r;
                top.clear();
            }
            if r == best_rank {
                top.push(c);
            }
        }
        match top.len() {
            0 => None,
            1 => Some(Hit::One(top[0], Via::Name)),
            _ => {
                let here = self.files[file as usize];
                top.sort_by_key(|&c| {
                    let f = self.files[self.nodes[c as usize].file as usize];
                    (Reverse(common_dir_prefix(here, f)), c)
                });
                Some(Hit::Many(top))
            }
        }
    }

    /// Binary search for `class.name` in the sorted methods vector.
    #[inline]
    fn own_method(&self, class: u32, name: &str) -> Option<u32> {
        let i = self
            .methods
            .partition_point(|&(c, n, _)| (c, n) < (class, name));
        match self.methods.get(i) {
            Some(&(c, n, m)) if c == class && n == name => Some(m),
            _ => None,
        }
    }

    /// BFS through `adj` (either parents or children) looking for the first
    /// class that defines `name`. `visited` also acts as a cycle guard;
    /// `MAX_CHAIN` bounds adversarial/deep hierarchies.
    fn walk(&self, start: u32, name: &str, adj: &Map<u32, Vec<u32>>) -> Option<u32> {
        let mut queue: VecDeque<u32> = adj.get(&start)?.iter().copied().collect();
        let mut visited: Vec<u32> = vec![start];
        while let Some(c) = queue.pop_front() {
            if visited.contains(&c) {
                continue;
            }
            visited.push(c);
            if visited.len() > MAX_CHAIN {
                break;
            }
            if let Some(m) = self.own_method(c, name) {
                return Some(m);
            }
            if let Some(next) = adj.get(&c) {
                queue.extend(next.iter().copied());
            }
        }
        None
    }

    /// own methods -> ancestors (full BFS) -> descendants (overrides)
    ///
    /// Ancestors first because inherited methods are the common case;
    /// descendants second so an override in a subclass can also be found
    /// when the call site is on the base (e.g. Python's `super().foo()`).
    fn method_in_hierarchy(&self, class: u32, name: &str) -> Option<u32> {
        self.own_method(class, name)
            .or_else(|| self.walk(class, name, &self.parents))
            .or_else(|| self.walk(class, name, &self.children))
    }

    fn resolve_call(
        &self,
        callee: &str,
        file: u32,
        class: Option<u32>,
        has_self: bool,
    ) -> Option<Hit> {
        // Exact full-ID match always wins — no ambiguity possible.
        if let Some(&i) = self.node_map.get(callee) {
            return Some(Hit::One(i, Via::Local));
        }
        if callee.is_empty() || callee.contains('/') {
            return None;
        }
        let (qual, name) = split_callee(callee);
        if name.is_empty() {
            return None;
        }

        // Unqualified: `foo()`
        let Some(q) = qual else {
            // If the enclosing method has a self param, try the class chain
            // first — `foo()` inside a method could be a sibling method.
            // Not in Python / JS / TS: there a sibling needs `self.` / `this.`,
            // and a bare `foo()` is a module-level function.
            let fam = self.file_family[file as usize];
            if has_self && fam != 1 && fam != 2 {
                if let Some(m) = class.and_then(|c| self.method_in_hierarchy(c, name)) {
                    return Some(Hit::One(m, Via::Local));
                }
            }
            return self.lookup(name, file, Want::Call);
        };

        // `self.foo()` / `this.bar()` / `cls.baz()` / `super().foo()`
        if is_self_qualifier(q) {
            if let Some(m) = class.and_then(|c| self.method_in_hierarchy(c, name)) {
                return Some(Hit::One(m, Via::Local));
            }
            return self.lookup(name, file, Want::MethodCall);
        }

        // `f(x).foo()`: the receiver is an expression we cannot type.
        if q == "()" {
            return self.lookup(name, file, Want::MethodCall);
        }

        // pkg.Func() / module.func(): look up the head of the qualifier in
        // the file's namespace imports and, if it maps to project files,
        // resolve `name` inside those files only.
        let root = q.split(sep).next().unwrap_or(q);
        match self.imports[file as usize].namespaces.get(root) {
            Some(Some(fs)) => {
                if let Some(x) = self.lookup_in_files(name, fs, file, Want::Call, 0) {
                    return Some(Hit::One(x, Via::Import));
                }
            }
            Some(None) if self.strict_imports => {
                return None; // fmt.Println, os.path.join, ...
            }
            _ => {}
        }

        // Class.staticMethod() / Class::method(): resolve the qualifier as
        // a class first, then search that class's method hierarchy.
        let q_last = q.rsplit(sep).next().unwrap_or(q);
        if let Some(Hit::One(cls, via)) = self.lookup(q_last, file, Want::Class) {
            if let Some(m) = self.method_in_hierarchy(cls, name) {
                return Some(Hit::One(m, via));
            }
        }
        self.lookup(name, file, Want::MethodCall)
    }

    fn resolve_base(&self, base: &str, file: u32) -> Option<u32> {
        if let Some(&i) = self.node_map.get(base) {
            return Some(i);
        }
        // `Base<T>` / `Base[]` / `Base(args)` -> `Base`. Generic args and
        // array suffixes are irrelevant to *which class* the base refers to.
        let base = base.split(['<', '[', '(']).next().unwrap_or(base).trim();
        let (qual, name) = split_callee(base);
        if let Some(q) = qual {
            let root = q.split(sep).next().unwrap_or(q);
            if let Some(Some(fs)) = self.imports[file as usize].namespaces.get(root) {
                if let Some(x) = self.lookup_in_files(name, fs, file, Want::Class, 0) {
                    return Some(x);
                }
            }
        }
        self.lookup(name, file, Want::Class).map(|h| h.best())
    }
}

// v2 exists because v1's global-first-match symbol index gets calls
// wrong whenever two unrelated classes define a method with the same
// short name common enough in real codebases (`__init__`, `run`,
// `handle`) that a class-aware, scope-aware resolver earns its extra
// cost for callers who need accuracy over raw speed.
pub fn build_call_graph_v2(structure: &HashMap<String, FileData>) -> CallGraph {
    build_with(structure, &CallGraphOptions::default())
}

pub fn build_with(structure: &HashMap<String, FileData>, opts: &CallGraphOptions) -> CallGraph {
    if structure.is_empty() {
        return CallGraph {
            nodes: Vec::new(),
            edges: Vec::new(),
        };
    }

    // 0. Deterministic file order, grouped by directory.
    //
    // Two invariants come out of this:
    //   * `paths` is sorted by (dir, path), which means file indices are
    //     grouped by directory. `file_dir` is therefore non-decreasing,
    //     which is what the partition_point tiers in `lookup` rely on.
    //   * "First wins" on duplicate IDs is deterministic across runs.
    let mut files: Vec<(&str, &FileData)> =
        structure.iter().map(|(k, v)| (k.as_str(), v)).collect();
    files.sort_unstable_by(|a, b| (dir_of(a.0), a.0).cmp(&(dir_of(b.0), b.0)));
    let paths: Vec<&str> = files.iter().map(|f| f.0).collect();
    let file_family: Vec<u8> = files
        .iter()
        .map(|f| language_family(&f.1.language))
        .collect();
    let mut file_dir: Vec<u32> = Vec::with_capacity(paths.len());
    {
        let (mut prev, mut id) = (None::<&str>, 0u32);
        for p in &paths {
            let d = dir_of(p);
            if matches!(prev, Some(pd) if pd != d) {
                id += 1;
            }
            prev = Some(d);
            file_dir.push(id);
        }
    }
    // Chunking matters here: one Rayon task per file would spend most of
    // its time on scheduling. `threads * 8` gives the pool enough work to
    // stay fed while keeping per-task `Vec`s small enough for cache.
    let threads = rayon::current_num_threads().max(1);
    let chunk = (files.len() / (threads * 8)).clamp(16, 2048);
    let module_index = build_module_index(&paths);

    // 1. Nodes, class->base refs and resolved imports (parallel, order-preserving).
    let extracts: Vec<Extract> = files
        .par_chunks(chunk)
        .enumerate()
        .map(|(ci, slice)| {
            let mut ex = Extract {
                nodes: Vec::with_capacity(slice.len() * 8),
                bases: Vec::new(),
                imports: Vec::with_capacity(slice.len()),
            };
            for (j, &(_, fd)) in slice.iter().enumerate() {
                let f = (ci * chunk + j) as u32;
                ex.imports
                    .push(build_file_imports(fd, slice[j].0, &module_index));
                for func in &fd.functions {
                    ex.nodes.push(Node {
                        id: &func.id,
                        name: node_name(&func.name, &func.id),
                        kind: if func.id.starts_with("method_") {
                            Kind::Method
                        } else {
                            Kind::Function
                        },
                        file: f,
                        is_entry: func.tags.iter().any(|t| t.as_str() == ENTRY_TAG),
                        owner: None,
                    });
                }
                for class in &fd.classes {
                    ex.nodes.push(Node {
                        id: &class.id,
                        name: node_name(&class.name, &class.id),
                        kind: Kind::Class,
                        file: f,
                        is_entry: false,
                        owner: None,
                    });
                    for base in &class.bases {
                        ex.bases.push(BaseRef {
                            class: &class.id,
                            base: base.as_str(),
                            file: f,
                            line: class.line_start as u32,
                        });
                    }
                    for m in &class.methods {
                        ex.nodes.push(Node {
                            id: &m.id,
                            name: node_name(&m.name, &m.id),
                            kind: Kind::Method,
                            file: f,
                            is_entry: false,
                            owner: Some(&class.id),
                        });
                    }
                }
            }
            ex
        })
        .collect();

    // 2. Sequential merge: first node (in sorted file order) wins a duplicate id.
    //
    // The merge is single-threaded because it populates a global map. It
    // is still fast — all the expensive per-file work already happened in
    // step 1. If two parser outputs disagree on an ID, the earlier file
    // (per sort order) wins, so the result is deterministic.
    let mut nodes: Vec<Node> = Vec::new();
    let mut node_map: Map<&str, u32> = Map::new();
    let mut base_refs: Vec<BaseRef> = Vec::new();
    let mut imports: Vec<FileImports> = Vec::with_capacity(files.len());
    for ex in extracts {
        for n in ex.nodes {
            if let Entry::Vacant(v) = node_map.entry(n.id) {
                v.insert(nodes.len() as u32);
                nodes.push(n);
            }
        }
        base_refs.extend(ex.bases);
        imports.extend(ex.imports);
    }

    let mut by_name: Map<&str, Vec<u32>> = Map::with_capacity(nodes.len());
    for (i, n) in nodes.iter().enumerate() {
        by_name.entry(n.name).or_default().push(i as u32);
    }
    // Class-method index, sorted for binary search by (class, name).
    let mut methods: Vec<(u32, &str, u32)> = nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| {
            let owner = *node_map.get(n.owner?)?;
            Some((owner, n.name, i as u32))
        })
        .collect();
    methods.sort_unstable();

    let mut r = Resolver {
        nodes: &nodes,
        node_map: &node_map,
        by_name: &by_name,
        files: &paths,
        file_dir: &file_dir,
        file_family: &file_family,
        imports: &imports,
        methods: &methods,
        parents: Map::new(),
        children: Map::new(),
        max_ambiguous: opts.max_ambiguous,
        strict_imports: opts.strict_imports,
    };

    // 3. Inheritance edges, then the class hierarchy used by method lookup.
    //
    // Inheritance has to be resolved and materialised before calls, because
    // `resolve_call` walks `parents`/`children` to find inherited methods.
    // The edges are also sorted and deduped by (from, to) before being
    // stored — a class inheriting the same base twice (impossible in
    // valid source, possible in sloppy parser output) becomes one edge.
    let inherit: Vec<RawEdge> = {
        let mut v: Vec<RawEdge> = base_refs
            .par_iter()
            .filter_map(|b| {
                let child = *r.node_map.get(b.class)?;
                let parent = r.resolve_base(b.base, b.file)?;
                (child != parent).then_some(RawEdge {
                    from: child,
                    to: parent,
                    line: b.line,
                    kind: EDGE_INHERIT,
                    conditional: false,
                    via: Via::Local,
                })
            })
            .collect();
        v.sort_unstable_by_key(|e| (e.from, e.to, e.line));
        v.dedup_by_key(|e| (e.from, e.to));
        v
    };
    for e in &inherit {
        r.parents.entry(e.from).or_default().push(e.to);
        r.children.entry(e.to).or_default().push(e.from);
    }

    // 4. Call edges.
    //
    // Parallel across chunks again. Each chunk writes into its own `out`
    // and `buf`, so no locks are needed. `flush_edges` collapses multiple
    // calls to the same target from one caller into a single edge.
    let call_edges: Vec<RawEdge> = files
        .par_chunks(chunk)
        .enumerate()
        .flat_map_iter(|(ci, slice)| {
            let mut out: Vec<RawEdge> = Vec::new();
            let mut buf: Vec<RawEdge> = Vec::new();
            for (j, &(_, fd)) in slice.iter().enumerate() {
                let f = (ci * chunk + j) as u32;
                for func in &fd.functions {
                    let Some(&from) = r.node_map.get(func.id.as_str()) else {
                        continue;
                    };
                    for call in &func.calls {
                        if let Some(hit) = r.resolve_call(&call.callee, f, None, false) {
                            push_hit(&mut buf, from, hit, call);
                        }
                    }
                    flush_edges(&mut out, &mut buf);
                }
                for class in &fd.classes {
                    let Some(&cidx) = r.node_map.get(class.id.as_str()) else {
                        continue;
                    };
                    for m in &class.methods {
                        let Some(&from) = r.node_map.get(m.id.as_str()) else {
                            continue;
                        };
                        // `has_self` enables the "is this a sibling method?"
                        // shortcut in `resolve_call`.
                        let has_self = first_self_param(&m.params);
                        for call in &m.calls {
                            if let Some(hit) = r.resolve_call(&call.callee, f, Some(cidx), has_self)
                            {
                                push_hit(&mut buf, from, hit, call);
                            }
                        }
                        flush_edges(&mut out, &mut buf);
                    }
                }
            }
            out.into_iter()
        })
        .collect();

    // 5. Materialise output.
    //
    // `call_count_estimate` is the number of *resolved* call edges that
    // point at the node. It ignores inheritance edges on purpose — for
    // "hot spot" queries what matters is callers, not subclasses — and
    // by-name guesses (`name`, `ambiguous`): `dict.items()` must not make
    // the project's only `def items` a hot spot.
    let mut in_calls = vec![0u32; nodes.len()];
    for e in call_edges.iter().filter(|e| e.via < Via::Name) {
        in_calls[e.to as usize] += 1;
    }
    let out_nodes: Vec<CallGraphNode> = nodes
        .par_iter()
        .enumerate()
        .map(|(i, n)| CallGraphNode {
            id: n.id.to_string(),
            node_type: match n.kind {
                Kind::Function => "function",
                Kind::Method => "method",
                Kind::Class => "class",
            }
            .to_string(),
            file: paths[n.file as usize].to_string(),
            is_entry_point: n.is_entry,
            call_count_estimate: in_calls[i] as usize,
        })
        .collect();
    let out_edges: Vec<CallGraphEdge> = inherit
        .par_iter()
        .chain(call_edges.par_iter())
        .map(|e| CallGraphEdge {
            from: nodes[e.from as usize].id.to_string(),
            to: nodes[e.to as usize].id.to_string(),
            edge_type: if e.kind == EDGE_INHERIT {
                "inheritance"
            } else {
                "call"
            }
            .to_string(),
            conditional: e.conditional,
            call_site_line: e.line as usize,
            resolution: if e.kind == EDGE_INHERIT {
                String::new()
            } else {
                e.via.as_str().to_string()
            },
        })
        .collect();

    CallGraph {
        nodes: out_nodes,
        edges: out_edges,
    }
}

fn push_hit(
    buf: &mut Vec<RawEdge>,
    from: u32,
    hit: Hit,
    call: &crate::struc::kb_struct::FunctionCall,
) {
    let edge = |to: u32, via: Via| RawEdge {
        from,
        to,
        line: call.line as u32,
        kind: EDGE_CALL,
        conditional: call.is_conditional,
        via,
    };
    match hit {
        Hit::One(to, via) => buf.push(edge(to, via)),
        Hit::Many(all) => buf.extend(all.into_iter().map(|to| edge(to, Via::Ambiguous))),
    }
}

pub fn populate_called_by_from_graph(kb: &mut KnowledgeBase) {
    // Reverse edges are built from the *materialised* graph rather than
    // re-running resolution, so this can run in a separate pass after the
    // graph has been written to disk and reloaded.
    let g = &kb.call_graph;
    let file_of: HashMap<&str, &str> = g
        .nodes
        .iter()
        .map(|n| (n.id.as_str(), n.file.as_str()))
        .collect();
    let mut rev: HashMap<&str, Vec<CallerInfo>> = HashMap::new();
    for e in g.edges.iter().filter(|e| e.edge_type == "call") {
        rev.entry(e.to.as_str()).or_default().push(CallerInfo {
            function: e.from.clone(),
            file: file_of
                .get(e.from.as_str())
                .map_or_else(String::new, |f| f.to_string()),
            line: e.call_site_line,
            resolution: e.resolution.clone(),
        });
    }
    for fd in kb.structure.values_mut() {
        for f in &mut fd.functions {
            f.called_by = rev.remove(f.id.as_str()).unwrap_or_default();
        }
        for c in &mut fd.classes {
            for m in &mut c.methods {
                m.called_by = rev.remove(m.id.as_str()).unwrap_or_default();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    // #![expect(clippy::expect_used)]
    // #![expect(clippy::unwrap_used)]

    use super::*;

    mod first_self_param_tests {
        use super::*;

        fn p(name: &str) -> Parameter {
            Parameter {
                name: name.to_string(),
                type_annotation: String::new(),
                default_value: None,
            }
        }

        #[test]
        fn recognizes_all_known_receiver_spellings() {
            for name in ["self", "this", "cls", "_self", "self_", "myself"] {
                assert!(first_self_param(&[p(name)]), "{name} should be recognized");
            }
        }

        #[test]
        fn empty_params_is_false() {
            assert!(!first_self_param(&[]));
        }

        #[test]
        fn only_the_first_param_is_checked() {
            // a receiver-like name in second position must NOT count
            assert!(!first_self_param(&[p("other"), p("self")]));
        }

        #[test]
        fn case_sensitivity_gap() {
            assert!(!first_self_param(&[p("Self")]));
            assert!(!first_self_param(&[p("This")]));
            assert!(!first_self_param(&[p("Cls")]));
        }

        #[test]
        fn near_miss_spellings_rejected() {
            for name in ["self1", "SELF", "s_elf", " self", "self ", "__self__"] {
                assert!(!first_self_param(&[p(name)]), "{name} should NOT match");
            }
        }
    }
}

// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0
//
//! C# parser (tree-sitter-c-sharp).
//!
//! Types (class, record, struct, interface, enum, delegate) become `Class`
//! entries; methods, constructors and properties with a body become methods
//! of their type; fields, properties, events, enum members and primary
//! constructor parameters become attributes. Top-level statements become a
//! synthetic `Main` function.
//!
//! Calls are recorded as written (`Foo`, `this.Foo`, `x.Foo`, `A.B.Foo`,
//! `new T`), with one addition: when the receiver of `x.Foo()` is a
//! parameter or a local whose type is spelled out (`IssueTransition t`,
//! `var t = new IssueTransition(..)`), `defined_in` carries that type, and
//! `"var"` when it is a local of unknown type. A receiver that is not a
//! local (a field, a property, a primary constructor parameter) is left to
//! PRISM v2, which sees every part of a partial class.
//!
//! Constructor parameters (primary or explicit) of a class or struct are
//! recorded as calls with context `"inject"`: the class depends on that
//! type, which is how "who uses service X" is answered for DI.
//!
//! What this cannot know without Roslyn: overloads (all overloads of a name
//! share one id, the first wins in the graph), `var` initialised from
//! anything but `new T(..)` / `GetRequiredService<T>()`, and members reached
//! through a chain (`a.B.C()`).

use super::utils::{extract_todos, static_regex};

use crate::struc::kb_struct::*;
use crate::utils::syntax;
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::LazyLock;
use tree_sitter::{Node, Parser};

static SECURITY_PATTERNS: LazyLock<Vec<(Regex, &'static str, &'static str)>> = LazyLock::new(
    || {
        vec![
            (
                static_regex(r"FromSqlRaw\(|ExecuteSqlRaw\(|ExecuteSqlRawAsync\(|new SqlCommand\("),
                "sql_injection",
                "Raw SQL: check that it is not built from input",
            ),
            (
                static_regex(r"Process\.Start\("),
                "command_execution",
                "System command execution",
            ),
            (
                static_regex(
                    r"BinaryFormatter|NetDataContractSerializer|TypeNameHandling\.(All|Auto|Objects)",
                ),
                "unsafe_deserialization",
                "Unsafe deserialization",
            ),
            (
                static_regex(
                    r"\b(MD5|SHA1|DES|RC2|TripleDES)\.Create\(|new (MD5|SHA1)CryptoServiceProvider",
                ),
                "weak_crypto",
                "Weak or broken cryptographic algorithm",
            ),
            (
                static_regex(r"new Random\("),
                "weak_random",
                "Non-cryptographic random number generator",
            ),
            (
                static_regex(r#"(?i)(password|passwd|secret|api[_-]?key)\s*=\s*"[^"]+""#),
                "hardcoded_credential",
                "Hardcoded credential or secret",
            ),
            (
                static_regex(
                    r"ServerCertificateCustomValidationCallback|ServerCertificateValidationCallback|DangerousAcceptAnyServerCertificateValidator",
                ),
                "trust_manager",
                "Custom TLS certificate validation",
            ),
        ]
    },
);

static XML_TAG_RE: LazyLock<Regex> = LazyLock::new(|| static_regex(r"<[^>]+>"));

/// Name keywords -> tag, as in the other parsers.
const TAG_RULES: &[(&[&str], &str)] = &[
    (
        &["init", "setup", "initialize", "bootstrap"],
        "initialization",
    ),
    (&["dispose", "cleanup", "close", "shutdown"], "cleanup"),
    (
        &[
            "auth", "login", "logout", "password", "token", "encrypt", "decrypt",
        ],
        "authentication",
    ),
    (&["validate", "check", "verify", "sanitize"], "validation"),
    (
        &["repository", "query", "insert", "update", "delete", "save"],
        "database",
    ),
    (&["log", "logger"], "logging"),
    (&["parse", "decode"], "parsing"),
    (&["serialize", "encode"], "serialization"),
    (&["cache"], "caching"),
    (
        &["event", "listener", "handler", "subscribe"],
        "event-driven",
    ),
    (&["config", "options", "setting"], "configuration"),
];

const HTTP_VERBS: &[(&str, &str)] = &[
    ("HttpGet", "GET"),
    ("HttpPost", "POST"),
    ("HttpPut", "PUT"),
    ("HttpDelete", "DELETE"),
    ("HttpPatch", "PATCH"),
    ("HttpHead", "HEAD"),
    ("HttpOptions", "OPTIONS"),
];

const TEST_ATTRS: &[&str] = &[
    "Fact",
    "Theory",
    "Test",
    "TestMethod",
    "TestCase",
    "DataTestMethod",
];

/// Service-locator calls whose generic argument is the returned type:
/// `var s = sp.GetRequiredService<T>()` types `s` as `T`.
const LOCATORS: &[&str] = &[
    "GetRequiredService",
    "GetService",
    "GetRequiredKeyedService",
    "GetKeyedService",
];

/// Container registrations: `services.AddScoped<IFoo, Foo>()` wires up
/// every type it names.
const REGISTRATIONS: &[&str] = &[
    "AddScoped",
    "AddSingleton",
    "AddTransient",
    "AddHostedService",
    "AddKeyedScoped",
    "AddKeyedSingleton",
    "AddKeyedTransient",
    "TryAddScoped",
    "TryAddSingleton",
    "TryAddTransient",
];

fn child_of_kind<'t>(node: &Node<'t>, kind: &str) -> Option<Node<'t>> {
    let mut cursor = node.walk();
    let found = node.children(&mut cursor).find(|c| c.kind() == kind);
    found
}

fn children_of_kind<'t>(node: &Node<'t>, kind: &str) -> Vec<Node<'t>> {
    let mut cursor = node.walk();
    node.children(&mut cursor)
        .filter(|c| c.kind() == kind)
        .collect()
}

/// `global::A.B.C<T>?[]` -> `A.B.C`: the type a receiver or a base names,
/// without what does not change which declaration it is.
pub fn simple_type(t: &str) -> String {
    let t = t.trim();
    let t = t.strip_prefix("global::").unwrap_or(t);
    let t = t.split('<').next().unwrap_or(t);
    t.trim_end_matches(['?', '[', ']', ' ']).trim().to_string()
}

/// Name of an attribute as it is usually spelled: `[Microsoft.X.FactAttribute(..)]`
/// -> `Fact`.
fn attribute_name(attr: &str) -> &str {
    let a = attr.trim_start_matches('[').trim_end_matches(']').trim();
    let a = a.split('(').next().unwrap_or(a).trim();
    let a = a.rsplit('.').next().unwrap_or(a);
    a.strip_suffix("Attribute").unwrap_or(a)
}

/// First string argument of an attribute: `[HttpGet("{id}")]` -> `{id}`.
fn attribute_template(attr: &str) -> Option<String> {
    let open = attr.find('(')?;
    let rest = &attr[open + 1..];
    let start = rest.find('"')?;
    let rest = &rest[start + 1..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

fn join_route(prefix: Option<&str>, tmpl: Option<&str>) -> Option<String> {
    match (prefix, tmpl) {
        (_, Some(t)) if t.starts_with('/') || t.starts_with("~/") => {
            Some(t.trim_start_matches('~').to_string())
        }
        (Some(p), Some(t)) if !t.is_empty() => Some(format!(
            "{}/{}",
            p.trim_end_matches('/'),
            t.trim_start_matches('/')
        )),
        (Some(p), _) => Some(p.to_string()),
        (None, Some(t)) => Some(t.to_string()),
        (None, None) => None,
    }
}

#[derive(Default)]
struct Modifiers {
    access: Option<String>,
    rest: Vec<String>,
}

impl Modifiers {
    fn has(&self, m: &str) -> bool {
        self.rest.iter().any(|x| x == m)
    }
}

/// Names visible inside one member body: parameters and locals with their
/// declared type (`"var"` when it is not spelled out), local functions.
#[derive(Default)]
struct Scope {
    locals: HashMap<String, String>,
    local_fns: HashSet<String>,
}

/// Where a type is declared: what its members need to know about it.
struct TypeCtx<'c> {
    ns: Option<&'c str>,
    qual: &'c str,
    name: &'c str,
    kind: &'c str,
    route: Option<&'c str>,
}

pub struct CSharpParser<'s> {
    src: &'s str,
    file: String,
}

impl<'s> CSharpParser<'s> {
    pub fn new(src: &'s str, file: String) -> Self {
        Self { src, file }
    }

    fn text(&self, n: &Node) -> &'s str {
        n.utf8_text(self.src.as_bytes()).unwrap_or("")
    }

    pub fn parse(&self) -> Result<FileData, String> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_c_sharp::LANGUAGE.into())
            .map_err(|e| format!("Failed to load C# grammar: {}", e))?;
        let tree = parser
            .parse(self.src, None)
            .ok_or_else(|| "Failed to parse C# file".to_string())?;
        let root = tree.root_node();

        let imports = self.extract_imports(&root);
        let mut classes = Vec::new();
        let mut functions = Vec::new();
        self.walk_container(&root, None, &mut Vec::new(), &mut classes);

        let globals = children_of_kind(&root, "global_statement");
        if !globals.is_empty() {
            functions.push(self.top_level_main(&globals));
        }

        Ok(FileData {
            language: "csharp".to_string(),
            loc: self.src.lines().count(),
            imports,
            functions,
            classes,
            global_vars: vec![],
            todos: extract_todos(self.src),
            security_notes: self.detect_security_patterns(),
            syntax: syntax::inspect(&tree),
        })
    }

    // ───────────────────────────── usings ─────────────────────────────

    fn extract_imports(&self, root: &Node) -> Vec<Import> {
        let own_root = self.first_namespace(root);
        let mut out = Vec::new();
        let mut stack = vec![*root];
        while let Some(node) = stack.pop() {
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                match child.kind() {
                    "using_directive" => {
                        if let Some(imp) = self.parse_using(&child, own_root.as_deref()) {
                            out.push(imp);
                        }
                    }
                    "namespace_declaration" | "declaration_list" => stack.push(child),
                    _ => {}
                }
            }
        }
        out
    }

    fn first_namespace(&self, root: &Node) -> Option<String> {
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if matches!(
                child.kind(),
                "namespace_declaration" | "file_scoped_namespace_declaration"
            ) {
                return child
                    .child_by_field_name("name")
                    .map(|n| self.text(&n).to_string());
            }
        }
        None
    }

    fn parse_using(&self, node: &Node, own_ns: Option<&str>) -> Option<Import> {
        let alias = node
            .child_by_field_name("name")
            .map(|n| self.text(&n).to_string());
        let mut module = None;
        let mut modifiers = Vec::new();
        let mut cursor = node.walk();
        for (i, child) in node.children(&mut cursor).enumerate() {
            match child.kind() {
                "global" => modifiers.push("global".to_string()),
                "static" => modifiers.push("static".to_string()),
                "qualified_name" | "identifier" | "alias_qualified_name" | "generic_name"
                    if node.field_name_for_child(i as u32) != Some("name") =>
                {
                    module = Some(self.text(&child).to_string());
                }
                _ => {}
            }
        }
        let module = module?;
        let module = module
            .strip_prefix("global::")
            .unwrap_or(&module)
            .to_string();
        let head = module.split('.').next().unwrap_or("");
        let import_type = if head == "System" || head == "Microsoft" {
            "stdlib"
        } else if own_ns.is_some_and(|ns| ns.split('.').next() == Some(head)) {
            "internal"
        } else {
            "external"
        };
        Some(Import {
            module,
            items: vec![],
            import_type: import_type.to_string(),
            alias,
            modifiers,
            ..Default::default()
        })
    }

    // ───────────────────────────── types ─────────────────────────────

    /// Compilation unit, namespace body or type body: types declared in it.
    fn walk_container(
        &self,
        node: &Node,
        ns: Option<&str>,
        stack: &mut Vec<String>,
        classes: &mut Vec<Class>,
    ) {
        // `namespace A.B;` is a sibling of the declarations it covers.
        let mut current_ns: Option<String> = ns.map(str::to_string);
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "file_scoped_namespace_declaration" => {
                    current_ns = child
                        .child_by_field_name("name")
                        .map(|n| self.qualify_ns(ns, self.text(&n)));
                }
                "namespace_declaration" => {
                    let inner = child
                        .child_by_field_name("name")
                        .map(|n| self.qualify_ns(current_ns.as_deref(), self.text(&n)));
                    if let Some(body) = child.child_by_field_name("body") {
                        self.walk_container(&body, inner.as_deref(), stack, classes);
                    }
                }
                "class_declaration"
                | "struct_declaration"
                | "record_declaration"
                | "interface_declaration"
                | "enum_declaration"
                | "delegate_declaration" => {
                    self.type_declaration(&child, current_ns.as_deref(), stack, None, classes);
                }
                _ => {}
            }
        }
    }

    fn qualify_ns(&self, outer: Option<&str>, name: &str) -> String {
        match outer {
            Some(o) if !o.is_empty() => format!("{o}.{name}"),
            _ => name.to_string(),
        }
    }

    fn modifiers(&self, node: &Node) -> Modifiers {
        let mut m = Modifiers::default();
        for child in children_of_kind(node, "modifier") {
            let t = self.text(&child);
            match t {
                "public" | "private" | "protected" | "internal" | "file" => {
                    m.access = Some(match m.access.take() {
                        Some(prev) => format!("{prev} {t}"),
                        None => t.to_string(),
                    });
                }
                _ => m.rest.push(t.to_string()),
            }
        }
        m
    }

    fn attributes(&self, node: &Node) -> Vec<String> {
        let mut out = Vec::new();
        for list in children_of_kind(node, "attribute_list") {
            for attr in children_of_kind(&list, "attribute") {
                out.push(format!("[{}]", self.text(&attr)));
            }
        }
        out
    }

    /// `/// <summary>..</summary>` lines (or a block comment) right above a
    /// declaration, XML tags dropped.
    fn doc_comment(&self, node: &Node) -> String {
        let mut lines = Vec::new();
        let mut prev = node.prev_sibling();
        while let Some(p) = prev {
            if p.kind() != "comment" {
                break;
            }
            lines.push(self.text(&p));
            prev = p.prev_sibling();
        }
        lines.reverse();
        let joined = lines
            .iter()
            .flat_map(|c| c.lines())
            .map(|l| {
                l.trim()
                    .trim_start_matches('/')
                    .trim_start_matches('*')
                    .trim_end_matches("*/")
                    .trim()
            })
            .filter(|l| !l.is_empty())
            .collect::<Vec<_>>()
            .join(" ");
        XML_TAG_RE
            .replace_all(&joined, "")
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn type_params(&self, node: &Node) -> Vec<String> {
        child_of_kind(node, "type_parameter_list")
            .map(|tp| {
                let mut c = tp.walk();
                tp.named_children(&mut c)
                    .map(|n| self.text(&n).to_string())
                    .collect()
            })
            .unwrap_or_default()
    }

    fn type_declaration(
        &self,
        node: &Node,
        ns: Option<&str>,
        stack: &mut Vec<String>,
        outer_route: Option<&str>,
        classes: &mut Vec<Class>,
    ) {
        let Some(name_node) = node.child_by_field_name("name") else {
            return;
        };
        let name = self.text(&name_node).to_string();
        let (kind, prefix) = match node.kind() {
            "class_declaration" => ("class", "class_"),
            "struct_declaration" => ("struct", "struct_"),
            "record_declaration" if child_of_kind(node, "struct").is_some() => {
                ("record_struct", "struct_")
            }
            "record_declaration" => ("record", "class_"),
            "interface_declaration" => ("interface", "interface_"),
            "enum_declaration" => ("enum", "enum_"),
            _ => ("delegate", "type_"),
        };
        let qual = if stack.is_empty() {
            name.clone()
        } else {
            format!("{}.{}", stack.join("."), name)
        };
        let full_name = match ns {
            Some(n) if !n.is_empty() => format!("{n}.{qual}"),
            _ => qual.clone(),
        };
        let mods = self.modifiers(node);
        let attrs = self.attributes(node);
        let route_attr = attrs
            .iter()
            .find(|a| attribute_name(a) == "Route")
            .and_then(|a| attribute_template(a));
        let route = join_route(outer_route, route_attr.as_deref());

        let mut bases = Vec::new();
        if let Some(bl) = child_of_kind(node, "base_list") {
            let mut c = bl.walk();
            for b in bl.named_children(&mut c) {
                let t = if b.kind() == "primary_constructor_base_type" {
                    b.child_by_field_name("type")
                        .map(|t| self.text(&t))
                        .unwrap_or_default()
                } else {
                    self.text(&b)
                };
                if !t.is_empty() {
                    bases.push(t.to_string());
                }
            }
        }

        let ctx = TypeCtx {
            ns,
            qual: &qual,
            name: &name,
            kind,
            route: route.as_deref(),
        };
        let mut methods = Vec::new();
        let mut attributes = Vec::new();
        let mut nested = Vec::new();

        // Primary constructor: `class C(IFoo foo)`, `record R(int X)`.
        if kind != "delegate" {
            if let Some(plist) = child_of_kind(node, "parameter_list") {
                let params = self.parameters(&plist);
                for p in &params {
                    attributes.push(Attribute {
                        name: p.name.clone(),
                        type_annotation: p.type_annotation.clone(),
                        value: p.default_value.clone(),
                    });
                }
                methods.push(self.primary_constructor(node, &ctx, params));
            }
        }

        if let Some(body) = node.child_by_field_name("body") {
            let mut c = body.walk();
            for member in body.children(&mut c) {
                match member.kind() {
                    "method_declaration" => {
                        if let Some(f) = self.method(&member, &ctx) {
                            methods.push(f);
                        }
                    }
                    "constructor_declaration" => {
                        if let Some(f) = self.constructor(&member, &ctx) {
                            methods.push(f);
                        }
                    }
                    "property_declaration" => {
                        let (attr, f) = self.property(&member, &ctx);
                        attributes.extend(attr);
                        methods.extend(f);
                    }
                    "field_declaration" | "event_field_declaration" => {
                        attributes.extend(self.fields(&member));
                    }
                    "event_declaration" => {
                        if let Some(n) = member.child_by_field_name("name") {
                            attributes.push(Attribute {
                                name: self.text(&n).to_string(),
                                type_annotation: format!(
                                    "event {}",
                                    member
                                        .child_by_field_name("type")
                                        .map(|t| self.text(&t))
                                        .unwrap_or_default()
                                ),
                                value: None,
                            });
                        }
                    }
                    "enum_member_declaration" => {
                        if let Some(n) = member.child_by_field_name("name") {
                            attributes.push(Attribute {
                                name: self.text(&n).to_string(),
                                type_annotation: "enum_member".to_string(),
                                value: member
                                    .child_by_field_name("value")
                                    .map(|v| self.text(&v).to_string()),
                            });
                        }
                    }
                    "class_declaration"
                    | "struct_declaration"
                    | "record_declaration"
                    | "interface_declaration"
                    | "enum_declaration"
                    | "delegate_declaration" => nested.push(member),
                    _ => {}
                }
            }
        }

        let mut decorators = attrs.clone();
        decorators.push(kind.to_string());
        let info = CSharpInfo {
            namespace: ns.map(str::to_string),
            full_name: Some(full_name),
            kind: kind.to_string(),
            access_modifier: mods.access.clone(),
            is_partial: mods.has("partial"),
            is_static: mods.has("static"),
            modifiers: mods.rest,
            attributes: attrs,
            generic_params: self.type_params(node),
            route: route.clone(),
            ..Default::default()
        };
        classes.push(Class {
            id: format!("{prefix}{qual}::{}", self.file),
            name: name.clone(),
            bases,
            docstring: self.doc_comment(node),
            line_start: node.start_position().row + 1,
            line_end: node.end_position().row + 1,
            methods,
            attributes,
            decorators,
            lang_info: LanguageSpecificInfo {
                csharp: Some(Box::new(info)),
                ..Default::default()
            },
        });

        stack.push(name);
        for n in nested {
            self.type_declaration(&n, ns, stack, route.as_deref(), classes);
        }
        stack.pop();
    }

    fn fields(&self, node: &Node) -> Vec<Attribute> {
        let is_event = node.kind() == "event_field_declaration";
        let Some(decl) = child_of_kind(node, "variable_declaration") else {
            return vec![];
        };
        let ty = decl
            .child_by_field_name("type")
            .map(|t| self.text(&t))
            .unwrap_or_default();
        let ty = if is_event {
            format!("event {ty}")
        } else {
            ty.to_string()
        };
        children_of_kind(&decl, "variable_declarator")
            .into_iter()
            .filter_map(|d| {
                let name = self.text(&d.child_by_field_name("name")?).to_string();
                let value = d.named_child(1).map(|v| self.text(&v).to_string());
                Some(Attribute {
                    name,
                    type_annotation: ty.clone(),
                    value,
                })
            })
            .collect()
    }

    // ───────────────────────────── members ─────────────────────────────

    fn parameters(&self, plist: &Node) -> Vec<Parameter> {
        children_of_kind(plist, "parameter")
            .into_iter()
            .map(|p| {
                let name = p
                    .child_by_field_name("name")
                    .map(|n| self.text(&n).to_string())
                    .unwrap_or_default();
                let mut ty = p
                    .child_by_field_name("type")
                    .map(|t| self.text(&t).to_string())
                    .unwrap_or_default();
                // `this` / `ref` / `out` / `params` are part of how the
                // parameter is passed; `this` is what makes an extension.
                let mods: Vec<&str> = children_of_kind(&p, "modifier")
                    .iter()
                    .map(|m| self.text(m))
                    .collect();
                if !mods.is_empty() {
                    ty = format!("{} {}", mods.join(" "), ty);
                }
                let text = self.text(&p);
                let default_value = text
                    .split_once('=')
                    .map(|(_, d)| d.trim().to_string())
                    .filter(|d| !d.is_empty());
                Parameter {
                    name,
                    type_annotation: ty,
                    default_value,
                }
            })
            .collect()
    }

    /// Calls of type `inject` for every constructor parameter of a class
    /// or struct: the class depends on that type.
    fn injections(&self, plist: Option<&Node>, ctx: &TypeCtx) -> Vec<FunctionCall> {
        if !matches!(ctx.kind, "class" | "struct") {
            return vec![];
        }
        self.injected_params(plist, false)
    }

    /// `marked_only`: just the parameters the container fills in a method
    /// call (`[FromServices] T t` in an action, `[FromKeyedServices]`).
    fn injected_params(&self, plist: Option<&Node>, marked_only: bool) -> Vec<FunctionCall> {
        let Some(plist) = plist else { return vec![] };
        children_of_kind(plist, "parameter")
            .into_iter()
            .filter_map(|p| {
                if marked_only
                    && !self
                        .attributes(&p)
                        .iter()
                        .any(|a| matches!(attribute_name(a), "FromServices" | "FromKeyedServices"))
                {
                    return None;
                }
                let t = p.child_by_field_name("type")?;
                if t.kind() == "predefined_type" {
                    return None;
                }
                let ty = simple_type(self.text(&t));
                let last = ty.rsplit('.').next().unwrap_or(&ty);
                if !last.starts_with(|c: char| c.is_ascii_uppercase()) {
                    return None;
                }
                Some(FunctionCall {
                    callee: ty,
                    defined_in: None,
                    line: p.start_position().row + 1,
                    args: vec![],
                    is_conditional: false,
                    context: "inject".to_string(),
                })
            })
            .collect()
    }

    fn primary_constructor(&self, node: &Node, ctx: &TypeCtx, params: Vec<Parameter>) -> Function {
        let plist = child_of_kind(node, "parameter_list");
        let calls = self.injections(plist.as_ref(), ctx);
        let mut info = CSharpInfo {
            kind: "constructor".to_string(),
            is_primary_constructor: true,
            ..Default::default()
        };
        info.namespace = ctx.ns.map(str::to_string);
        let line = node.start_position().row + 1;
        Function {
            id: format!("method_{}_{}::{}", ctx.qual, ctx.name, self.file),
            name: ctx.name.to_string(),
            signature: format!("{}({})", ctx.name, self.param_list_text(&params)),
            variables: self.param_variables(&params),
            params,
            line_start: line,
            line_end: line,
            calls,
            complexity: 1,
            tags: vec!["constructor".to_string(), "primary-constructor".to_string()],
            importance_score: 0.55,
            lang_info: LanguageSpecificInfo {
                csharp: Some(Box::new(info)),
                ..Default::default()
            },
            ..Default::default()
        }
    }

    fn param_list_text(&self, params: &[Parameter]) -> String {
        params
            .iter()
            .map(|p| format!("{} {}", p.type_annotation, p.name))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn param_variables(&self, params: &[Parameter]) -> Vec<Variable> {
        params
            .iter()
            .map(|p| Variable {
                name: p.name.clone(),
                var_type: Some(p.type_annotation.clone()).filter(|t| !t.is_empty()),
                scope: "param".to_string(),
                defined_at: None,
                transformations: vec![],
                used_in: vec![],
                returned: false,
            })
            .collect()
    }

    fn method(&self, node: &Node, ctx: &TypeCtx) -> Option<Function> {
        let name = self.text(&node.child_by_field_name("name")?).to_string();
        let ret = node
            .child_by_field_name("returns")
            .or_else(|| node.child_by_field_name("type"))
            .map(|t| self.text(&t).to_string())
            .unwrap_or_default();
        let bodies: Vec<Node> = node.child_by_field_name("body").into_iter().collect();
        Some(self.member(node, ctx, name, "method", ret, &bodies, vec![]))
    }

    fn constructor(&self, node: &Node, ctx: &TypeCtx) -> Option<Function> {
        let plist = node.child_by_field_name("parameters");
        let extra = self.injections(plist.as_ref(), ctx);
        let bodies: Vec<Node> = node.child_by_field_name("body").into_iter().collect();
        let mut f = self.member(
            node,
            ctx,
            ctx.name.to_string(),
            "constructor",
            String::new(),
            &bodies,
            extra,
        );
        f.tags.push("constructor".to_string());
        f.tags.sort();
        f.tags.dedup();
        Some(f)
    }

    /// A property is an attribute of its type; one with code (accessor
    /// bodies, `=> expr`, an initializer that calls something) is also a
    /// method, so the calls it makes are in the graph.
    fn property(&self, node: &Node, ctx: &TypeCtx) -> (Option<Attribute>, Option<Function>) {
        let Some(name) = node.child_by_field_name("name").map(|n| self.text(&n)) else {
            return (None, None);
        };
        let ty = node
            .child_by_field_name("type")
            .map(|t| self.text(&t).to_string())
            .unwrap_or_default();
        let value = node.child_by_field_name("value");
        let attr = Attribute {
            name: name.to_string(),
            type_annotation: ty.clone(),
            value: value.map(|v| self.text(&v).to_string()),
        };
        let mut bodies: Vec<Node> = value.into_iter().collect();
        if let Some(acc) = node.child_by_field_name("accessors") {
            for a in children_of_kind(&acc, "accessor_declaration") {
                if let Some(b) = a.child_by_field_name("body") {
                    bodies.push(b);
                }
            }
        }
        let has_code = bodies.iter().any(|b| self.contains_call(b));
        if !has_code {
            return (Some(attr), None);
        }
        let mut f = self.member(node, ctx, name.to_string(), "property", ty, &bodies, vec![]);
        f.tags.push("property".to_string());
        f.tags.sort();
        f.tags.dedup();
        (Some(attr), Some(f))
    }

    fn contains_call(&self, node: &Node) -> bool {
        if matches!(
            node.kind(),
            "invocation_expression" | "object_creation_expression"
        ) {
            return true;
        }
        let mut c = node.walk();
        let found = node.children(&mut c).any(|ch| self.contains_call(&ch));
        found
    }

    #[allow(clippy::too_many_arguments)]
    fn member(
        &self,
        node: &Node,
        ctx: &TypeCtx,
        name: String,
        kind: &str,
        return_type: String,
        bodies: &[Node],
        extra_calls: Vec<FunctionCall>,
    ) -> Function {
        let mods = self.modifiers(node);
        let attrs = self.attributes(node);
        let params = node
            .child_by_field_name("parameters")
            .map(|p| self.parameters(&p))
            .unwrap_or_default();
        let is_extension = params
            .first()
            .is_some_and(|p| p.type_annotation.starts_with("this "));

        let mut scope = Scope::default();
        for p in &params {
            let ty = p
                .type_annotation
                .trim_start_matches("this ")
                .trim_start_matches("ref ")
                .trim_start_matches("out ")
                .trim_start_matches("in ")
                .trim_start_matches("params ");
            scope.locals.insert(p.name.clone(), simple_type(ty));
        }
        for b in bodies {
            self.collect_locals(b, &mut scope);
        }
        let mut calls = extra_calls;
        if kind == "method" {
            let plist = node.child_by_field_name("parameters");
            calls.extend(self.injected_params(plist.as_ref(), true));
        }
        let mut seen = HashSet::new();
        for b in bodies {
            self.collect_calls(b, &scope, &mut calls, &mut seen, "unconditional");
        }

        let mut variables = self.param_variables(&params);
        let mut locals: Vec<(&String, &String)> = scope
            .locals
            .iter()
            .filter(|(n, _)| !params.iter().any(|p| &p.name == *n))
            .collect();
        locals.sort();
        for (n, t) in locals {
            variables.push(Variable {
                name: n.clone(),
                var_type: Some(t.clone()).filter(|t| t != "var"),
                scope: "local".to_string(),
                defined_at: None,
                transformations: vec![],
                used_in: vec![],
                returned: false,
            });
        }

        let mut control_flow = ControlFlow::default();
        let mut raises = Vec::new();
        let mut handles = Vec::new();
        for b in bodies {
            self.control_structures(b, &mut control_flow, &mut raises, &mut handles);
        }
        let complexity = 1 + bodies
            .iter()
            .map(|b| self.decision_points(b))
            .sum::<usize>();
        control_flow.complexity = complexity;

        // Routes and tests.
        let mut http_methods = Vec::new();
        let mut method_tmpl: Option<String> = None;
        let mut has_route = false;
        for a in &attrs {
            let an = attribute_name(a);
            if let Some((_, verb)) = HTTP_VERBS.iter().find(|(n, _)| *n == an) {
                http_methods.push(verb.to_string());
                if method_tmpl.is_none() {
                    method_tmpl = attribute_template(a);
                }
                has_route = true;
            } else if an == "Route" {
                method_tmpl = attribute_template(a).or(method_tmpl);
                has_route = true;
            }
        }
        let route = if has_route {
            join_route(ctx.route, method_tmpl.as_deref())
        } else {
            None
        };
        let is_test = attrs
            .iter()
            .any(|a| TEST_ATTRS.contains(&attribute_name(a)));
        let is_async = mods.has("async");

        let mut tags = Vec::new();
        let lower = name.to_lowercase();
        for (kws, tag) in TAG_RULES {
            if kws.iter().any(|k| lower.contains(k)) {
                tags.push(tag.to_string());
            }
        }
        if has_route {
            tags.push("api".to_string());
            tags.push("api-endpoint".to_string());
        }
        if is_test {
            tags.push("testing".to_string());
        }
        if is_extension {
            tags.push("extension-method".to_string());
        }
        if mods.has("override") {
            tags.push("override".to_string());
        }
        if is_async {
            tags.push("async".to_string());
        }
        if name == "Main" && mods.has("static") {
            tags.push("entry-point".to_string());
        }
        if attrs.iter().any(|a| attribute_name(a) == "Obsolete") {
            tags.push("deprecated".to_string());
        }
        tags.sort();
        tags.dedup();

        let mut importance: f32 = 0.5;
        match mods.access.as_deref() {
            Some("public") => importance += 0.1,
            Some("private") => importance -= 0.1,
            _ => {}
        }
        if has_route {
            importance += 0.2;
        }

        let sig_mods = mods
            .access
            .iter()
            .chain(mods.rest.iter())
            .cloned()
            .collect::<Vec<_>>()
            .join(" ");
        let signature = format!(
            "{} {} {}({})",
            sig_mods,
            return_type,
            name,
            self.param_list_text(&params)
        )
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .replace(" (", "(");

        let info = CSharpInfo {
            namespace: ctx.ns.map(str::to_string),
            kind: kind.to_string(),
            access_modifier: mods.access.clone(),
            is_static: mods.has("static"),
            is_extension,
            is_test,
            route,
            http_methods,
            attributes: attrs.clone(),
            generic_params: self.type_params(node),
            modifiers: mods.rest,
            ..Default::default()
        };

        Function {
            id: format!("method_{}_{}::{}", ctx.qual, name, self.file),
            name,
            signature,
            params,
            return_type,
            docstring: self.doc_comment(node),
            line_start: node.start_position().row + 1,
            line_end: node.end_position().row + 1,
            calls,
            called_by: vec![],
            variables,
            control_flow,
            exceptions: ExceptionInfo {
                raises,
                propagates: vec![],
                handles,
            },
            complexity,
            is_async,
            decorators: attrs,
            tags,
            importance_score: importance.clamp(0.0, 1.0),
            lang_info: LanguageSpecificInfo {
                csharp: Some(Box::new(info)),
                ..Default::default()
            },
        }
    }

    /// Top-level statements (`Program.cs`): one synthetic `Main`.
    fn top_level_main(&self, globals: &[Node]) -> Function {
        let mut scope = Scope::default();
        for g in globals {
            self.collect_locals(g, &mut scope);
        }
        let mut calls = Vec::new();
        let mut seen = HashSet::new();
        for g in globals {
            self.collect_calls(g, &scope, &mut calls, &mut seen, "unconditional");
        }
        let line_start = globals.first().map_or(1, |g| g.start_position().row + 1);
        let line_end = globals.last().map_or(1, |g| g.end_position().row + 1);
        Function {
            id: format!("func_Main::{}", self.file),
            name: "Main".to_string(),
            signature: "top-level statements".to_string(),
            line_start,
            line_end,
            calls,
            complexity: 1 + globals
                .iter()
                .map(|g| self.decision_points(g))
                .sum::<usize>(),
            tags: vec!["entry-point".to_string()],
            importance_score: 0.8,
            lang_info: LanguageSpecificInfo {
                csharp: Some(Box::new(CSharpInfo {
                    kind: "method".to_string(),
                    ..Default::default()
                })),
                ..Default::default()
            },
            ..Default::default()
        }
    }

    // ───────────────────────────── bodies ─────────────────────────────

    /// Type of `var x = <init>` when the initializer names it.
    fn inferred_type(&self, init: &Node) -> Option<String> {
        let mut init = *init;
        while matches!(init.kind(), "await_expression" | "parenthesized_expression") {
            init = init.named_child(0)?;
        }
        match init.kind() {
            "object_creation_expression" => init
                .child_by_field_name("type")
                .map(|t| simple_type(self.text(&t))),
            "cast_expression" => init
                .child_by_field_name("type")
                .map(|t| simple_type(self.text(&t))),
            "invocation_expression" => self.located_service(&init),
            _ => None,
        }
    }

    /// `sp.GetRequiredService<T>()` -> `T`.
    fn located_service(&self, call: &Node) -> Option<String> {
        let (method, args) = self.generic_call(call)?;
        if !LOCATORS.contains(&method) {
            return None;
        }
        args.into_iter().next()
    }

    /// Types a call resolves from or registers in the DI container.
    fn services_named(&self, call: &Node) -> Vec<String> {
        match self.generic_call(call) {
            Some((m, args)) if REGISTRATIONS.contains(&m) => args,
            Some((m, args)) if LOCATORS.contains(&m) => args.into_iter().take(1).collect(),
            _ => vec![],
        }
    }

    /// `x.M<A, B>(..)` -> (`M`, [`A`, `B`]).
    fn generic_call(&self, call: &Node) -> Option<(&'s str, Vec<String>)> {
        let f = call.child_by_field_name("function")?;
        let name = if f.kind() == "member_access_expression" {
            f.child_by_field_name("name")?
        } else {
            f
        };
        if name.kind() != "generic_name" {
            return None;
        }
        let id = child_of_kind(&name, "identifier")?;
        let list = child_of_kind(&name, "type_argument_list")?;
        let mut c = list.walk();
        let args = list
            .named_children(&mut c)
            .map(|a| simple_type(self.text(&a)))
            .collect();
        Some((self.text(&id), args))
    }

    fn declare(&self, scope: &mut Scope, name: Option<Node>, ty: Option<String>) {
        if let Some(n) = name {
            if n.kind() == "identifier" {
                scope
                    .locals
                    .entry(self.text(&n).to_string())
                    .or_insert_with(|| ty.unwrap_or_else(|| "var".to_string()));
            }
        }
    }

    fn declared_type(&self, t: Option<Node>) -> Option<String> {
        let t = t?;
        if t.kind() == "implicit_type" {
            None
        } else {
            Some(simple_type(self.text(&t)))
        }
    }

    fn collect_locals(&self, node: &Node, scope: &mut Scope) {
        match node.kind() {
            "variable_declaration" => {
                let ty = self.declared_type(node.child_by_field_name("type"));
                for d in children_of_kind(node, "variable_declarator") {
                    let t = ty.clone().or_else(|| {
                        let mut c = d.walk();
                        let init = d.named_children(&mut c).nth(1);
                        init.and_then(|i| self.inferred_type(&i))
                    });
                    self.declare(scope, d.child_by_field_name("name"), t);
                }
            }
            "foreach_statement" => {
                let ty = self.declared_type(node.child_by_field_name("type"));
                self.declare(scope, node.child_by_field_name("left"), ty);
            }
            "declaration_expression" | "declaration_pattern" | "catch_declaration" => {
                let ty = self.declared_type(node.child_by_field_name("type"));
                self.declare(scope, node.child_by_field_name("name"), ty);
            }
            "parameter" => {
                let ty = self.declared_type(node.child_by_field_name("type"));
                self.declare(scope, node.child_by_field_name("name"), ty);
            }
            "implicit_parameter" => {
                self.declare(scope, Some(*node), None);
            }
            "local_function_statement" => {
                if let Some(n) = node.child_by_field_name("name") {
                    scope.local_fns.insert(self.text(&n).to_string());
                }
            }
            _ => {}
        }
        let mut c = node.walk();
        for ch in node.children(&mut c) {
            self.collect_locals(&ch, scope);
        }
    }

    /// Qualifier of a call and, when the receiver is a declared local, its
    /// type (`"var"` if not spelled out).
    fn receiver(&self, expr: &Node, scope: &Scope) -> (String, Option<String>) {
        match expr.kind() {
            "this" | "this_expression" => ("this".to_string(), None),
            "base" | "base_expression" => ("base".to_string(), None),
            "identifier" => {
                let name = self.text(expr).to_string();
                let ty = scope.locals.get(&name).cloned();
                (name, ty)
            }
            "member_access_expression"
            | "qualified_name"
            | "alias_qualified_name"
            | "predefined_type" => {
                let t = self.text(expr);
                if t.chars()
                    .all(|c| c.is_alphanumeric() || c == '_' || c == '.' || c == ':')
                {
                    (t.strip_prefix("global::").unwrap_or(t).to_string(), None)
                } else {
                    ("()".to_string(), None)
                }
            }
            // `new T(..).F()`, `sp.GetRequiredService<T>().F()`, `((T)x).F()`.
            _ => ("()".to_string(), self.inferred_type(expr)),
        }
    }

    fn method_name(&self, n: &Node) -> Option<&'s str> {
        match n.kind() {
            "identifier" => Some(self.text(n)),
            "generic_name" => child_of_kind(n, "identifier").map(|i| self.text(&i)),
            _ => None,
        }
    }

    fn call_target(&self, f: &Node, scope: &Scope) -> Option<(String, Option<String>)> {
        match f.kind() {
            "identifier" | "generic_name" => {
                let name = self.method_name(f)?;
                if name == "nameof"
                    || scope.locals.contains_key(name)
                    || scope.local_fns.contains(name)
                {
                    return None; // a delegate or a local function
                }
                Some((name.to_string(), None))
            }
            "member_access_expression" => {
                let name = self.method_name(&f.child_by_field_name("name")?)?;
                let expr = f.child_by_field_name("expression")?;
                let (q, ty) = self.receiver(&expr, scope);
                Some((format!("{q}.{name}"), ty))
            }
            "conditional_access_expression" => {
                let binding = child_of_kind(f, "member_binding_expression")?;
                let name = self.method_name(&binding.child_by_field_name("name")?)?;
                let cond = f.child_by_field_name("condition")?;
                let (q, ty) = self.receiver(&cond, scope);
                Some((format!("{q}.{name}"), ty))
            }
            _ => None,
        }
    }

    /// Declared type of `T x = new(..)`.
    fn target_type(&self, node: &Node) -> Option<String> {
        let decl = node.parent()?.parent()?;
        if decl.kind() != "variable_declaration" {
            return None;
        }
        self.declared_type(decl.child_by_field_name("type"))
    }

    fn collect_calls(
        &self,
        node: &Node,
        scope: &Scope,
        out: &mut Vec<FunctionCall>,
        seen: &mut HashSet<(String, usize)>,
        context: &str,
    ) {
        let child_context = match node.kind() {
            "if_statement" => "if",
            "for_statement" | "foreach_statement" | "while_statement" | "do_statement" => "loop",
            "switch_statement" | "switch_expression" => "switch",
            "try_statement" => "try",
            "catch_clause" => "catch",
            "lambda_expression" | "anonymous_method_expression" => "lambda",
            _ => context,
        };
        let line = node.start_position().row + 1;
        let target = match node.kind() {
            "invocation_expression" => node
                .child_by_field_name("function")
                .and_then(|f| self.call_target(&f, scope)),
            "object_creation_expression" => node
                .child_by_field_name("type")
                .map(|t| (format!("new {}", simple_type(self.text(&t))), None)),
            "implicit_object_creation_expression" => {
                self.target_type(node).map(|t| (format!("new {t}"), None))
            }
            _ => None,
        };
        if node.kind() == "invocation_expression" {
            for t in self.services_named(node) {
                if seen.insert((t.clone(), line)) {
                    out.push(FunctionCall {
                        callee: t,
                        defined_in: None,
                        line,
                        args: vec![],
                        is_conditional: context != "unconditional",
                        context: "inject".to_string(),
                    });
                }
            }
        }
        if let Some((callee, defined_in)) = target {
            if seen.insert((callee.clone(), line)) {
                let args = node
                    .child_by_field_name("arguments")
                    .or_else(|| child_of_kind(node, "argument_list"))
                    .map(|a| {
                        let mut c = a.walk();
                        a.named_children(&mut c)
                            .map(|x| self.text(&x).to_string())
                            .collect()
                    })
                    .unwrap_or_default();
                out.push(FunctionCall {
                    callee,
                    defined_in,
                    line,
                    args,
                    is_conditional: context != "unconditional",
                    context: context.to_string(),
                });
            }
        }
        let mut c = node.walk();
        for ch in node.children(&mut c) {
            self.collect_calls(&ch, scope, out, seen, child_context);
        }
    }

    fn call_names(&self, node: &Node) -> Vec<String> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = vec![*node];
        while let Some(n) = stack.pop() {
            if n.kind() == "invocation_expression" {
                if let Some(f) = n.child_by_field_name("function") {
                    let name = match f.kind() {
                        "member_access_expression" => f.child_by_field_name("name"),
                        "conditional_access_expression" => {
                            child_of_kind(&f, "member_binding_expression")
                                .and_then(|b| b.child_by_field_name("name"))
                        }
                        _ => Some(f),
                    };
                    if let Some(name) = name.and_then(|n| self.method_name(&n)) {
                        if seen.insert(name) {
                            out.push(name.to_string());
                        }
                    }
                }
            }
            let mut c = n.walk();
            let kids: Vec<Node> = n.children(&mut c).collect();
            stack.extend(kids.into_iter().rev());
        }
        out
    }

    fn control_structures(
        &self,
        node: &Node,
        cf: &mut ControlFlow,
        raises: &mut Vec<String>,
        handles: &mut Vec<String>,
    ) {
        let line = node.start_position().row + 1;
        match node.kind() {
            "if_statement" => {
                if let Some(cons) = node.child_by_field_name("consequence") {
                    cf.branches.push(Branch {
                        branch_type: "if".to_string(),
                        condition: node
                            .child_by_field_name("condition")
                            .map(|c| self.text(&c).to_string())
                            .unwrap_or_default(),
                        line,
                        true_path: ExecutionPath {
                            calls: self.call_names(&cons),
                            returns: None,
                            raises: None,
                        },
                        false_path: node.child_by_field_name("alternative").map(|a| {
                            ExecutionPath {
                                calls: self.call_names(&a),
                                returns: None,
                                raises: None,
                            }
                        }),
                    });
                }
            }
            "for_statement" | "foreach_statement" | "while_statement" | "do_statement" => {
                cf.loops.push(Loop {
                    loop_type: match node.kind() {
                        "for_statement" => "for",
                        "foreach_statement" => "foreach",
                        "while_statement" => "while",
                        _ => "do-while",
                    }
                    .to_string(),
                    condition: node
                        .child_by_field_name("condition")
                        .or_else(|| node.child_by_field_name("right"))
                        .map(|c| self.text(&c).to_string())
                        .unwrap_or_default(),
                    line,
                    calls: self.call_names(node),
                });
            }
            "try_statement" => {
                let try_calls = node
                    .child_by_field_name("body")
                    .map(|b| self.call_names(&b))
                    .unwrap_or_default();
                let mut except_clauses = Vec::new();
                let mut finally_calls = Vec::new();
                let mut c = node.walk();
                for ch in node.children(&mut c) {
                    match ch.kind() {
                        "catch_clause" => except_clauses.push(ExceptClause {
                            exception_type: child_of_kind(&ch, "catch_declaration")
                                .and_then(|d| d.child_by_field_name("type"))
                                .map(|t| self.text(&t).to_string())
                                .unwrap_or_default(),
                            line: ch.start_position().row + 1,
                            calls: self.call_names(&ch),
                        }),
                        "finally_clause" => finally_calls = self.call_names(&ch),
                        _ => {}
                    }
                }
                cf.try_blocks.push(TryBlock {
                    line,
                    try_calls,
                    except_clauses,
                    finally_calls,
                });
            }
            "throw_statement" | "throw_expression" => {
                if let Some(e) = node.named_child(0) {
                    let t = if e.kind() == "object_creation_expression" {
                        e.child_by_field_name("type")
                            .map(|t| self.text(&t).to_string())
                            .unwrap_or_default()
                    } else {
                        self.text(&e).to_string()
                    };
                    if !t.is_empty() && !raises.contains(&t) {
                        raises.push(t);
                    }
                }
            }
            "catch_declaration" => {
                if let Some(t) = node.child_by_field_name("type") {
                    let t = self.text(&t).to_string();
                    if !handles.contains(&t) {
                        handles.push(t);
                    }
                }
            }
            _ => {}
        }
        let mut c = node.walk();
        for ch in node.children(&mut c) {
            self.control_structures(&ch, cf, raises, handles);
        }
    }

    fn decision_points(&self, node: &Node) -> usize {
        let mut n = match node.kind() {
            "if_statement"
            | "for_statement"
            | "foreach_statement"
            | "while_statement"
            | "do_statement"
            | "catch_clause"
            | "switch_section"
            | "switch_expression_arm"
            | "conditional_expression"
            | "&&"
            | "||"
            | "??" => 1,
            _ => 0,
        };
        let mut c = node.walk();
        for ch in node.children(&mut c) {
            n += self.decision_points(&ch);
        }
        n
    }

    fn detect_security_patterns(&self) -> Vec<SecurityNote> {
        let mut notes = Vec::new();
        for (idx, line) in self.src.lines().enumerate() {
            if let Some((_, t, d)) = SECURITY_PATTERNS
                .iter()
                .find(|(re, _, _)| re.is_match(line))
            {
                notes.push(SecurityNote {
                    note_type: t.to_string(),
                    line: idx + 1,
                    description: d.to_string(),
                });
            }
        }
        notes
    }
}

pub fn parse_source(path: &Path, source_code: &str) -> Result<(String, FileData), String> {
    let clean_path = path.strip_prefix("./").unwrap_or(path);
    let path_str = clean_path.to_string_lossy().to_string();
    let parser = CSharpParser::new(source_code, path_str.clone());
    let file_data = parser.parse()?;
    Ok((path_str, file_data))
}

pub fn parse_file(path: &Path) -> Result<(String, FileData), String> {
    let source_code = std::fs::read_to_string(path)
        .map_err(|e| format!("Failed to read file {}: {}", path.display(), e))?;
    parse_source(path, &source_code)
}

#[cfg(test)]
mod tests {
    #![expect(clippy::expect_used)]

    use super::*;

    fn parse(path: &str, src: &str) -> FileData {
        let (_, fd) =
            crate::grammar_files::parse_source(Path::new(path), src).expect("parse should succeed");
        fd
    }

    fn class<'a>(fd: &'a FileData, name: &str) -> &'a Class {
        #[allow(clippy::panic)]
        fd.classes
            .iter()
            .find(|c| c.name == name)
            .unwrap_or_else(|| panic!("type `{name}` not found"))
    }

    fn method<'a>(c: &'a Class, name: &str) -> &'a Function {
        #[allow(clippy::panic)]
        c.methods
            .iter()
            .find(|m| m.name == name)
            .unwrap_or_else(|| panic!("member `{name}` not found in {}", c.name))
    }

    fn calls(f: &Function) -> Vec<(&str, Option<&str>)> {
        f.calls
            .iter()
            .map(|c| (c.callee.as_str(), c.defined_in.as_deref()))
            .collect()
    }

    fn cs(c: &Class) -> &CSharpInfo {
        c.lang_info.csharp.as_deref().expect("csharp info")
    }

    const CONTROLLER: &str = r#"
using Microsoft.AspNetCore.Mvc;
using Pm.Api.Services;
using static Pm.Api.Util.Guards;
using Clock = Pm.Api.Util.SystemClock;
namespace Pm.Api.Controllers;

/// <summary>Issues over REST.</summary>
[ApiController]
[Route("rest/api/2/issue")]
public sealed partial class IssuesController(IssueTransition transition, ILogger<IssuesController> log)
    : ApiControllerBase, IDisposable
{
    private readonly AppDbContext _db;
    public event EventHandler? Changed;
    public int Count { get; set; }
    public string Title => Format(Count);
    public delegate void Handler(int x);

    [HttpPost("{key}/transitions")]
    public async Task<IActionResult> Move(string key, CancellationToken ct = default)
    {
        var issue = await _db.Issues.FindAsync(key);
        await sp.GetRequiredService<IssueTransition>().MoveAsync(issue, ct);
        var other = new IssueTransition(_db);
        IssueTransition typed = new(_db);
        await transition.MoveAsync(issue, ct);
        await other.MoveAsync(issue, ct);
        await typed.MoveAsync(issue, ct);
        foreach (var i in list) i.Touch();
        this.Helper();
        Helper();
        int Local(int a) => a;
        Local(1);
        return Ok(nameof(Move));
    }

    private static void Helper() {}
}

public record SearchDefinition(string Name, int Size);
public readonly record struct Point(int X);
public interface IFoo { void Bar(); }
public enum Color { Red = 1, Green }
public static class Ext { public static int Twice(this int x) => x * 2; }
"#;

    #[test]
    fn types_members_and_namespace() {
        let fd = parse("src/Pm.Api/Controllers/IssuesController.cs", CONTROLLER);
        assert_eq!(fd.language, "csharp");
        assert!(fd.syntax.is_clean(), "syntax: {:?}", fd.syntax);

        let ctl = class(&fd, "IssuesController");
        assert_eq!(
            ctl.id,
            "class_IssuesController::src/Pm.Api/Controllers/IssuesController.cs"
        );
        assert_eq!(ctl.bases, vec!["ApiControllerBase", "IDisposable"]);
        assert_eq!(ctl.docstring, "Issues over REST.");
        let info = cs(ctl);
        assert_eq!(info.namespace.as_deref(), Some("Pm.Api.Controllers"));
        assert_eq!(
            info.full_name.as_deref(),
            Some("Pm.Api.Controllers.IssuesController")
        );
        assert!(info.is_partial);
        assert_eq!(info.route.as_deref(), Some("rest/api/2/issue"));

        // Fields, events, properties and primary constructor parameters.
        let attrs: Vec<&str> = ctl.attributes.iter().map(|a| a.name.as_str()).collect();
        for a in ["transition", "log", "_db", "Changed", "Count", "Title"] {
            assert!(attrs.contains(&a), "{a} missing from {attrs:?}");
        }
        // A property with code is also a member with calls; an auto
        // property is not.
        assert!(method(ctl, "Title").tags.contains(&"property".to_string()));
        assert!(!ctl.methods.iter().any(|m| m.name == "Count"));

        // The primary constructor injects its class-typed parameters.
        let ctor = method(ctl, "IssuesController");
        assert_eq!(
            ctor.id,
            "method_IssuesController_IssuesController::src/Pm.Api/Controllers/IssuesController.cs"
        );
        let injected: Vec<&str> = ctor
            .calls
            .iter()
            .filter(|c| c.context == "inject")
            .map(|c| c.callee.as_str())
            .collect();
        assert_eq!(injected, vec!["IssueTransition", "ILogger"]);

        // Every kind of type.
        let kinds: Vec<(&str, &str)> = fd
            .classes
            .iter()
            .map(|c| (c.name.as_str(), cs(c).kind.as_str()))
            .collect();
        for k in [
            ("Handler", "delegate"),
            ("SearchDefinition", "record"),
            ("Point", "record_struct"),
            ("IFoo", "interface"),
            ("Color", "enum"),
            ("Ext", "class"),
        ] {
            assert!(kinds.contains(&k), "{k:?} missing from {kinds:?}");
        }
        assert_eq!(
            class(&fd, "Handler").id,
            "type_IssuesController.Handler::src/Pm.Api/Controllers/IssuesController.cs"
        );
        assert_eq!(
            class(&fd, "Point").id.split("::").next(),
            Some("struct_Point")
        );
        // Records' positional parameters are their properties; a record
        // does not inject.
        let rec = class(&fd, "SearchDefinition");
        assert_eq!(rec.attributes.len(), 2);
        assert!(method(rec, "SearchDefinition").calls.is_empty());
        assert!(cs(class(&fd, "Ext")).is_static);
        let twice = method(class(&fd, "Ext"), "Twice");
        assert!(twice
            .lang_info
            .csharp
            .as_ref()
            .is_some_and(|i| i.is_extension));
    }

    #[test]
    fn calls_record_receiver_types_of_locals() {
        let fd = parse("Controllers/IssuesController.cs", CONTROLLER);
        let mv = method(class(&fd, "IssuesController"), "Move");
        assert_eq!(
            calls(mv),
            vec![
                ("_db.Issues.FindAsync", None),
                // The receiver is a service-locator call: typed by its
                // generic argument.
                ("().MoveAsync", Some("IssueTransition")),
                // ... and a use of the service, as an injection is.
                ("IssueTransition", None),
                ("sp.GetRequiredService", None),
                ("new IssueTransition", None),
                ("new IssueTransition", None),
                // A primary constructor parameter is not a local: the
                // resolver types it from the class.
                ("transition.MoveAsync", None),
                ("other.MoveAsync", Some("IssueTransition")),
                ("typed.MoveAsync", Some("IssueTransition")),
                ("i.Touch", Some("var")),
                ("this.Helper", None),
                ("Helper", None),
                ("Ok", None),
            ]
        );
    }

    #[test]
    fn attributes_routes_and_tests() {
        let fd = parse("Controllers/IssuesController.cs", CONTROLLER);
        let mv = method(class(&fd, "IssuesController"), "Move");
        assert_eq!(mv.decorators, vec!["[HttpPost(\"{key}/transitions\")]"]);
        let info = mv.lang_info.csharp.as_deref().expect("info");
        assert_eq!(
            info.route.as_deref(),
            Some("rest/api/2/issue/{key}/transitions")
        );
        assert_eq!(info.http_methods, vec!["POST"]);
        assert!(mv.tags.contains(&"api-endpoint".to_string()));
        assert!(mv.is_async);

        let t = parse(
            "tests/Pm.Tests/IssueTests.cs",
            "namespace Pm.Tests;\npublic class IssueTests {\n  [Fact]\n  public void Moves() { }\n  \
             [Theory, InlineData(1)]\n  public void Many(int x) { }\n}\n",
        );
        let c = class(&t, "IssueTests");
        for name in ["Moves", "Many"] {
            let m = method(c, name);
            assert!(
                m.tags.contains(&"testing".to_string()),
                "{name}: {:?}",
                m.tags
            );
        }
        assert_eq!(
            method(c, "Many").decorators,
            vec!["[Theory]", "[InlineData(1)]"]
        );
    }

    #[test]
    fn usings_and_top_level_statements() {
        let fd = parse(
            "src/Pm.Api/Program.cs",
            "global using Pm.Shared;\nusing static Pm.Util.Guards;\nusing Pm.Api.Services;\n\
             using Alias = Pm.Other.Thing;\n\
             var builder = WebApplication.CreateBuilder(args);\n\
             builder.Services.AddPmServices();\nvar app = builder.Build();\napp.Run();\n",
        );
        let imps: Vec<(&str, Vec<&str>, Option<&str>)> = fd
            .imports
            .iter()
            .map(|i| {
                (
                    i.module.as_str(),
                    i.modifiers.iter().map(String::as_str).collect(),
                    i.alias.as_deref(),
                )
            })
            .collect();
        assert_eq!(
            imps,
            vec![
                ("Pm.Shared", vec!["global"], None),
                ("Pm.Util.Guards", vec!["static"], None),
                ("Pm.Api.Services", vec![], None),
                ("Pm.Other.Thing", vec![], Some("Alias")),
            ]
        );
        assert_eq!(fd.functions.len(), 1);
        let main = &fd.functions[0];
        assert_eq!(main.id, "func_Main::src/Pm.Api/Program.cs");
        assert!(main.tags.contains(&"entry-point".to_string()));
        let callees: Vec<&str> = main.calls.iter().map(|c| c.callee.as_str()).collect();
        assert_eq!(
            callees,
            vec![
                "WebApplication.CreateBuilder",
                "builder.Services.AddPmServices",
                "builder.Build",
                "app.Run"
            ]
        );
    }

    #[test]
    fn services_injected_into_constructors_actions_and_located() {
        let fd = parse(
            "AgentsController.cs",
            "public class AgentsController(IssueTransition t, int retries) : ControllerBase {\n\
             \x20 public AgentsController(AgentHandover h, string name) : this(null, 0) {}\n\
             \x20 public Task ForIssue(string key, [FromServices] AgentHandover handover, Repo plain)\n\
             \x20   => sp.GetService<IClock>().Now();\n\
             \x20 static void Wire(IServiceCollection s) => s.AddScoped<IIssueService, IssueService>();\n}\n\
             public record Dto(Issue Issue);\n",
        );
        let injected = |c: &Class, m: &str| -> Vec<String> {
            method(c, m)
                .calls
                .iter()
                .filter(|c| c.context == "inject")
                .map(|c| c.callee.clone())
                .collect()
        };
        let ctl = class(&fd, "AgentsController");
        let ctors: Vec<Vec<String>> = ctl
            .methods
            .iter()
            .filter(|m| m.name == "AgentsController")
            .map(|m| {
                m.calls
                    .iter()
                    .filter(|c| c.context == "inject")
                    .map(|c| c.callee.clone())
                    .collect()
            })
            .collect();
        assert_eq!(ctors, vec![vec!["IssueTransition"], vec!["AgentHandover"]]);
        // Only the `[FromServices]` parameter of an action is injected.
        assert_eq!(injected(ctl, "ForIssue"), vec!["AgentHandover", "IClock"]);
        assert!(injected(class(&fd, "Dto"), "Dto").is_empty());
        // A registration names both the service and its implementation.
        assert_eq!(injected(ctl, "Wire"), vec!["IIssueService", "IssueService"]);
    }

    #[test]
    fn block_namespaces_and_nested_types() {
        let fd = parse(
            "a.cs",
            "namespace A { namespace B { public class Outer { public class Inner { void M() {} } } } }",
        );
        let inner = class(&fd, "Inner");
        assert_eq!(inner.id, "class_Outer.Inner::a.cs");
        assert_eq!(cs(inner).full_name.as_deref(), Some("A.B.Outer.Inner"));
        assert_eq!(method(inner, "M").id, "method_Outer.Inner_M::a.cs");
    }
}

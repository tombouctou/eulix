// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

use libeulix::struc::kb_struct::*;

/// Modifiers PRISM v2 reads to link an interface / virtual method to its
/// implementations and overrides.
const DISPATCH_MODIFIERS: [&str; 5] = ["abstract", "virtual", "override", "sealed", "static"];

/// The part of `CSharpInfo` the analysis still reads once a file is parsed:
/// PRISM v2 merges partial types by `full_name`, resolves `using` through
/// `namespace` and extension calls through `is_extension`, dispatch through
/// `kind` and the override modifiers; entry points read `route` /
/// `http_methods`.
fn slim_csharp(info: &mut LanguageSpecificInfo) {
    let kept = info.csharp.take().map(|c| {
        let mut modifiers = c.modifiers;
        modifiers.retain(|m| DISPATCH_MODIFIERS.contains(&m.as_str()));
        Box::new(CSharpInfo {
            namespace: c.namespace,
            full_name: c.full_name,
            kind: c.kind,
            modifiers,
            is_static: c.is_static,
            is_partial: c.is_partial,
            is_extension: c.is_extension,
            route: c.route,
            http_methods: c.http_methods,
            ..Default::default()
        })
    });
    *info = LanguageSpecificInfo {
        csharp: kept,
        ..Default::default()
    };
}

/// `keep_receivers`: C# calls carry the receiver's declared type in
/// `defined_in` and constructor injection in `context`; PRISM v2 reads both.
pub fn strip_fn(f: &mut Function, keep_receivers: bool) {
    f.control_flow = ControlFlow::default();
    f.exceptions = ExceptionInfo::default();
    if keep_receivers {
        slim_csharp(&mut f.lang_info);
    } else {
        f.lang_info = LanguageSpecificInfo::default();
    }
    f.called_by = Vec::new();
    for c in &mut f.calls {
        c.args = Vec::new();
        if !keep_receivers {
            c.context = String::new();
            c.defined_in = None;
        }
    }
    f.calls.shrink_to_fit();
}

pub fn strip_emitted(fd: &mut FileData) {
    fn strip_fn(f: &mut Function) {
        f.signature = String::new();
        f.return_type = String::new();
        f.variables = Vec::new();
        f.params.truncate(1); // analyzer only reads params[0] (self detection)
        f.params.shrink_to_fit();
    }
    let csharp = fd.language == "csharp";
    fd.todos = Vec::new();
    fd.functions.iter_mut().for_each(strip_fn);
    for c in &mut fd.classes {
        if csharp {
            // Member types (`_db: AppDbContext`) type the receivers of calls.
            for a in &mut c.attributes {
                a.value = None;
            }
            slim_csharp(&mut c.lang_info);
        } else {
            c.attributes = Vec::new();
            c.lang_info = LanguageSpecificInfo::default();
        }
        c.methods.iter_mut().for_each(strip_fn);
    }
}

pub fn slim(fd: &mut FileData) {
    let csharp = fd.language == "csharp";
    fd.global_vars = Vec::new();
    fd.security_notes = Vec::new();
    // Imports stay: PRISM v2 resolves calls through them. Dropping them here
    // left every call to be matched by bare name. They are small next to the
    // functions, and kb.json does not carry them (see views.rs).
    fd.imports.shrink_to_fit();
    fd.functions.iter_mut().for_each(|f| strip_fn(f, csharp));
    for c in &mut fd.classes {
        c.methods.iter_mut().for_each(|f| strip_fn(f, csharp));
        c.methods.shrink_to_fit();
    }
    fd.functions.shrink_to_fit();
    fd.classes.shrink_to_fit();
}

#[cfg(test)]
mod tests {
    #![allow(clippy::expect_used)]

    use super::*;
    use std::path::Path;

    fn parsed(path: &str, src: &str) -> FileData {
        let (_, mut fd) =
            libeulix::grammar_files::parse_source(Path::new(path), src).expect("fixture parses");
        slim(&mut fd);
        strip_emitted(&mut fd);
        fd
    }

    #[test]
    fn csharp_keeps_what_prism_v2_reads() {
        let fd = parsed(
            "Svc.cs",
            "namespace A;\npublic partial class Svc(Repo repo) {\n\
             \x20 private readonly Clock _clock = new();\n\
             \x20 public void Run(Repo r) { r.Save(); }\n}\n",
        );
        let c = &fd.classes[0];
        let info = c.lang_info.csharp.as_deref().expect("type info kept");
        assert_eq!(info.full_name.as_deref(), Some("A.Svc"));
        assert!(info.is_partial);
        let members: Vec<(&str, &str, bool)> = c
            .attributes
            .iter()
            .map(|a| {
                (
                    a.name.as_str(),
                    a.type_annotation.as_str(),
                    a.value.is_some(),
                )
            })
            .collect();
        assert_eq!(
            members,
            vec![("repo", "Repo", false), ("_clock", "Clock", false)]
        );
        let run = c.methods.iter().find(|m| m.name == "Run").expect("Run");
        assert_eq!(run.calls[0].defined_in.as_deref(), Some("Repo"));
        assert!(run.calls[0].args.is_empty());
        let ctor = c.methods.iter().find(|m| m.name == "Svc").expect("ctor");
        assert_eq!(ctor.calls[0].context, "inject");
    }

    #[test]
    fn csharp_keeps_the_modifiers_dispatch_reads() {
        let fd = parsed(
            "Base.cs",
            "namespace A;\npublic abstract class Base {\n\
             \x20 protected internal abstract Task Run();\n\
             \x20 public static async void Make() {}\n}\n",
        );
        let mods = |name: &str| {
            let m = fd.classes[0].methods.iter().find(|m| m.name == name);
            m.and_then(|m| m.lang_info.csharp.as_deref())
                .map(|i| (i.modifiers.clone(), i.is_static, i.access_modifier.clone()))
        };
        assert_eq!(
            mods("Run"),
            Some((vec!["abstract".to_string()], false, None))
        );
        assert_eq!(mods("Make"), Some((vec!["static".to_string()], true, None)));
        let class = fd.classes[0]
            .lang_info
            .csharp
            .as_deref()
            .map(|i| (i.kind.clone(), i.modifiers.clone()));
        assert_eq!(
            class,
            Some(("class".to_string(), vec!["abstract".to_string()]))
        );
    }

    #[test]
    fn other_languages_are_slimmed_as_before() {
        let fd = parsed(
            "a.py",
            "class A:\n    x: int = 1\n    def f(self, o):\n        o.g(1)\n",
        );
        let c = &fd.classes[0];
        assert!(c.attributes.is_empty());
        assert!(c.methods[0].calls[0].defined_in.is_none());
        assert!(c.methods[0].calls[0].context.is_empty());
    }
}

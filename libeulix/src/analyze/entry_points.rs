// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

/// Find entry points (main functions, app init, etc.)
///
/// Deliberately name/decorator-based rather than framework-specific
/// parsing: supporting every framework's exact entry-point convention
/// individually isn't tractable, so this leans on naming conventions
/// (`main`, `run`, `start`) and common decorator keywords that are
/// shared across most web/CLI frameworks instead.
use crate::struc::kb_struct::{EntryPoint, KnowledgeBase};

pub fn find_entry_points(kb: &KnowledgeBase) -> Vec<EntryPoint> {
    let mut entry_points = Vec::new();

    for (filepath, filedata) in &kb.structure {
        for func in &filedata.functions {
            if func.name == "main" || func.name == "run" || func.name == "start" {
                entry_points.push(EntryPoint {
                    entry_type: "main".to_string(),
                    path: None,
                    function: func.name.clone(),
                    handler: func.name.clone(),
                    file: filepath.clone(),
                    line: func.line_start,
                    methods: None,
                });
            }

            // Substring matching on decorator text (rather than parsing
            // each framework's decorator syntax) keeps this working
            // across Flask/FastAPI/etc. without per-framework branches.
            for decorator in &func.decorators {
                if decorator.contains("route")
                    || decorator.contains("get")
                    || decorator.contains("post")
                    || decorator.contains("api")
                {
                    let route_path = extract_route_path(decorator);
                    let http_methods = extract_http_methods(decorator);

                    entry_points.push(EntryPoint {
                        entry_type: "api_endpoint".to_string(),
                        path: route_path,
                        function: func.name.clone(),
                        handler: func.name.clone(),
                        file: filepath.clone(),
                        line: func.line_start,
                        methods: Some(http_methods),
                    });
                }
            }

            if func
                .decorators
                .iter()
                .any(|d| d.contains("command") || d.contains("click"))
            {
                entry_points.push(EntryPoint {
                    entry_type: "cli_command".to_string(),
                    path: Some(func.name.clone()),
                    function: func.name.clone(),
                    handler: func.name.clone(),
                    file: filepath.clone(),
                    line: func.line_start,
                    methods: None,
                });
            }
        }

        // C# controller actions: the parser has already joined the
        // controller's `[Route]` with the action's `[HttpGet("..")]`.
        for class in &filedata.classes {
            for m in &class.methods {
                let Some(info) = m.lang_info.csharp.as_deref() else {
                    continue;
                };
                let Some(route) = &info.route else { continue };
                entry_points.push(EntryPoint {
                    entry_type: "api_endpoint".to_string(),
                    path: Some(route.clone()),
                    function: format!("{}.{}", class.name, m.name),
                    handler: m.id.clone(),
                    file: filepath.clone(),
                    line: m.line_start,
                    methods: Some(if info.http_methods.is_empty() {
                        vec!["ANY".to_string()]
                    } else {
                        info.http_methods.clone()
                    }),
                });
            }
        }
    }

    entry_points
}

fn extract_route_path(decorator: &str) -> Option<String> {
    // A regex on quoted, path-like text is good enough to pull the
    // route string out of arbitrary decorator syntax without writing a
    // real parser for every framework's decorator grammar.
    let re = regex::Regex::new(r#"['"]([/\w-]+)['"]"#).ok()?;
    re.captures(decorator)
        .and_then(|caps| caps.get(1))
        .map(|m| m.as_str().to_string())
}

fn extract_http_methods(decorator: &str) -> Vec<String> {
    let mut methods = Vec::new();
    let dec_lower = decorator.to_lowercase();

    if dec_lower.contains("get") {
        methods.push("GET".to_string());
    }
    if dec_lower.contains("post") {
        methods.push("POST".to_string());
    }
    if dec_lower.contains("put") {
        methods.push("PUT".to_string());
    }
    if dec_lower.contains("delete") {
        methods.push("DELETE".to_string());
    }

    // GET is the safest default when no verb keyword is found, since
    // most undecorated/ambiguous route definitions in practice are
    // read-only endpoints.
    if methods.is_empty() {
        methods.push("GET".to_string());
    }

    methods
}

#[cfg(test)]
mod tests {
    #![expect(clippy::expect_used)]

    use super::*;
    use std::collections::HashMap;
    use std::path::Path;

    #[test]
    fn csharp_controller_actions_are_api_endpoints() {
        let src = "namespace Pm.Api.Controllers;\n[ApiController]\n[Route(\"rest/api/2/issue\")]\n\
                   public class IssuesController : ControllerBase {\n\
                   \x20 [HttpGet(\"{key}\")] public IActionResult Get(string key) => Ok();\n\
                   \x20 [HttpPost] public IActionResult Create() => Ok();\n\
                   \x20 public void NotAnAction() {}\n}\n";
        let (path, fd) =
            crate::grammar_files::parse_source(Path::new("Controllers/IssuesController.cs"), src)
                .expect("parses");
        let kb = KnowledgeBase {
            metadata: crate::struc::kb_struct::Metadata {
                version: String::new(),
                git_hash: String::new(),
                project_name: String::new(),
                project_hash: String::new(),
                parsed_at: String::new(),
                languages: vec![],
                total_files: 1,
                total_loc: 0,
                total_functions: 0,
                total_classes: 0,
                total_methods: 0,
            },
            structure: HashMap::from([(path, fd)]),
            call_graph: Default::default(),
            dependency_graph: Default::default(),
            indices: Default::default(),
            entry_points: vec![],
            external_dependencies: vec![],
            patterns: Default::default(),
        };
        let mut eps: Vec<(String, Vec<String>, String)> = find_entry_points(&kb)
            .into_iter()
            .map(|e| {
                (
                    e.path.unwrap_or_default(),
                    e.methods.unwrap_or_default(),
                    e.function,
                )
            })
            .collect();
        eps.sort();
        assert_eq!(
            eps,
            vec![
                (
                    "rest/api/2/issue".to_string(),
                    vec!["POST".to_string()],
                    "IssuesController.Create".to_string()
                ),
                (
                    "rest/api/2/issue/{key}".to_string(),
                    vec!["GET".to_string()],
                    "IssuesController.Get".to_string()
                ),
            ]
        );
    }
}

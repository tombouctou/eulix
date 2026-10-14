// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

use crate::struc::kb_struct::*;
use regex::Regex;
use std::sync::LazyLock;

#[allow(clippy::expect_used)] // patterns are compile-time literals; failure = programmer bug at first use
pub fn static_regex(pattern: &str) -> Regex {
    Regex::new(pattern).expect("static regex pattern must be valid")
}

static TODO_RE: LazyLock<Regex> = LazyLock::new(|| {
    static_regex(r"(?i)(?://|/\*).*?\b(?:TODO|FIXME|XXX)\b[:\s]*(.*?)(?:\*/\s*)?$")
});

pub fn extract_todos(source_code: &str) -> Vec<Todo> {
    source_code
        .lines()
        .enumerate()
        .filter_map(|(idx, line)| {
            TODO_RE.captures(line).and_then(|caps| {
                caps.get(1).map(|m| {
                    let text = m.as_str().trim().to_string();
                    let text_lower = text.to_lowercase();

                    let priority =
                        if text_lower.contains("critical") || text_lower.contains("urgent") {
                            "high"
                        } else if text_lower.contains("minor") {
                            "low"
                        } else {
                            "medium"
                        };

                    Todo {
                        line: idx + 1,
                        text,
                        priority: priority.to_string(),
                    }
                })
            })
        })
        .collect()
}

/// Callee text for the `function` node of a call, keeping a simple receiver
/// so the call-graph resolver can tell `m.f()` from `f()`:
///   `foo()`          -> `foo`
///   `a.b.foo()`      -> `a.b.foo`
///   `self.foo()` / `this.foo()` -> `self.foo` / `this.foo`
///   `super().foo()`  -> `super.foo`
///   `f(x).foo()` / `xs[0].foo()` -> `().foo`  (receiver is an expression)
///
/// Works for Python (`attribute`: object/attribute) and JS/TS
/// (`member_expression`: object/property). Anything else falls back to the
/// last dotted segment of the node text, the historical behaviour.
pub fn qualified_callee(func: &tree_sitter::Node, src: &[u8]) -> String {
    match func.kind() {
        "attribute" | "member_expression" => {
            let prop = func
                .child_by_field_name("attribute")
                .or_else(|| func.child_by_field_name("property"))
                .and_then(|n| n.utf8_text(src).ok())
                .unwrap_or("")
                .trim();
            if prop.is_empty() {
                return String::new();
            }
            let recv = func
                .child_by_field_name("object")
                .and_then(|o| receiver_path(&o, src))
                .unwrap_or_else(|| "()".to_string());
            format!("{recv}.{prop}")
        }
        _ => {
            let text = func.utf8_text(src).unwrap_or("");
            text.trim_start_matches("await ")
                .rsplit('.')
                .next()
                .unwrap_or(text)
                .trim()
                .to_string()
        }
    }
}

/// `a`, `a.b.c`, `this`, `super()` -> the dotted path; anything computed -> None.
fn receiver_path(node: &tree_sitter::Node, src: &[u8]) -> Option<String> {
    match node.kind() {
        "identifier" | "this" | "super" | "property_identifier" => {
            node.utf8_text(src).ok().map(str::to_string)
        }
        "attribute" | "member_expression" => {
            let obj = receiver_path(&node.child_by_field_name("object")?, src)?;
            let prop = node
                .child_by_field_name("attribute")
                .or_else(|| node.child_by_field_name("property"))?
                .utf8_text(src)
                .ok()?;
            Some(format!("{obj}.{prop}"))
        }
        // Python `super().foo()`: resolve through the class hierarchy.
        "call" => {
            let f = node.child_by_field_name("function")?;
            (f.utf8_text(src).ok()? == "super").then(|| "super".to_string())
        }
        _ => None,
    }
}

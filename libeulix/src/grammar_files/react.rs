// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

//! React helpers shared by the JavaScript and TypeScript grammars.
//!
//! JSX/TSX components call each other by *rendering* (`<Child />`), not by
//! `call_expression`, and are often defined through a wrapper
//! (`const X = memo(() => ...)`). Both shapes are invisible to a call graph
//! built from call expressions alone.

use tree_sitter::Node;

/// Wrappers whose first argument is the component itself.
const COMPONENT_WRAPPERS: [&str; 4] = ["memo", "forwardRef", "React.memo", "React.forwardRef"];

fn text<'s>(node: &Node, src: &'s [u8]) -> &'s str {
    node.utf8_text(src).unwrap_or_default()
}

/// The component rendered by a JSX element, as a callee name.
///
/// Only `jsx_opening_element` / `jsx_self_closing_element` count (the closing
/// tag would double every edge). Lowercase identifiers are intrinsic DOM
/// elements (`<div>`) and are skipped; `<Foo>` gives `Foo` and a member tag
/// (`<Dialog.Content>`) gives `Dialog.Content`, which the resolver treats as
/// a qualified call. Namespaced tags (`<svg:path>`) are not components.
pub fn jsx_component_name(node: &Node, src: &[u8]) -> Option<String> {
    if !matches!(
        node.kind(),
        "jsx_opening_element" | "jsx_self_closing_element"
    ) {
        return None;
    }
    let name = node.child_by_field_name("name")?;
    match name.kind() {
        "identifier" => {
            let n = text(&name, src);
            n.starts_with(|c: char| c.is_ascii_uppercase())
                .then(|| n.to_string())
        }
        "member_expression" | "nested_identifier" => {
            let n = text(&name, src);
            (!n.is_empty()).then(|| n.split_whitespace().collect())
        }
        _ => None,
    }
}

/// Peels `memo(...)`, `forwardRef(...)` (and their `React.` forms, nested in
/// any order) off a variable's initializer and returns the function inside.
/// Returns `value` unchanged when it is not such a wrapper, or when the
/// wrapped argument is not a function (e.g. `memo(Other)`).
pub fn unwrap_component_wrapper<'t>(value: Node<'t>, src: &[u8]) -> Node<'t> {
    let mut cur = value;
    while cur.kind() == "call_expression" {
        let Some(func) = cur.child_by_field_name("function") else {
            break;
        };
        if !COMPONENT_WRAPPERS.contains(&text(&func, src)) {
            break;
        }
        let Some(args) = cur.child_by_field_name("arguments") else {
            break;
        };
        let mut cursor = args.walk();
        let Some(first) = args.named_children(&mut cursor).next() else {
            break;
        };
        match first.kind() {
            "arrow_function" | "function_expression" | "function" => return first,
            "call_expression" => cur = first,
            _ => break,
        }
    }
    value
}

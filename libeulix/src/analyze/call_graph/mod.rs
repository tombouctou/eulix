// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

pub mod prism_v1;
pub mod prism_v2;

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::analyze::call_graph::prism_v1::build_call_graph;
    use crate::analyze::call_graph::prism_v2::build_call_graph_v2;
    use crate::struc::kb_struct::{Class, FileData, Function, FunctionCall};

    fn func(id: &str, name: &str, calls: Vec<&str>) -> Function {
        Function {
            id: id.to_string(),
            name: name.to_string(),
            calls: calls
                .into_iter()
                .map(|c| FunctionCall {
                    callee: c.to_string(),
                    defined_in: None,
                    line: 1,
                    args: vec![],
                    is_conditional: false,
                    context: "unconditional".to_string(),
                })
                .collect(),
            ..Default::default()
        }
    }

    fn filedata(functions: Vec<Function>, classes: Vec<Class>) -> FileData {
        FileData {
            functions,
            classes,
            ..Default::default()
        }
    }

    #[test]
    fn empty_project_produces_empty_graph_both_versions() {
        let structure: HashMap<String, FileData> = HashMap::new();
        let g1 = build_call_graph(&structure);
        let g2 = build_call_graph_v2(&structure);
        assert!(g1.nodes.is_empty() && g1.edges.is_empty());
        assert!(g2.nodes.is_empty() && g2.edges.is_empty());
    }

    #[test]
    fn self_recursive_function_produces_a_self_edge() {
        let mut structure = HashMap::new();
        structure.insert(
            "a.c".to_string(),
            filedata(vec![func("func_fact::a.c", "fact", vec!["fact"])], vec![]),
        );
        let g = build_call_graph_v2(&structure);
        assert!(g
            .edges
            .iter()
            .any(|e| e.from == "func_fact::a.c" && e.to == "func_fact::a.c"));
    }

    #[test]
    fn colliding_function_ids_across_files_silently_dedupe_to_one_node() {
        // In practice ids embed the file path so this shouldn't happen,
        // but IF an upstream parser ever produces two identical ids
        // (e.g. two files sharing a generated/templated id), node_map's
        // `insert` keeps whichever came first and the second is dropped
        // without any warning or error.
        let mut structure = HashMap::new();
        structure.insert(
            "a.c".to_string(),
            filedata(vec![func("func_dup::x", "dup", vec![])], vec![]),
        );
        structure.insert(
            "b.c".to_string(),
            filedata(vec![func("func_dup::x", "dup", vec![])], vec![]),
        );
        let g = build_call_graph_v2(&structure);
        let dup_nodes: Vec<_> = g.nodes.iter().filter(|n| n.id == "func_dup::x").collect();
        assert_eq!(
            dup_nodes.len(),
            1,
            "colliding ids silently collapse into a single node"
        );
    }

    #[test]
    fn ambiguous_short_name_resolves_to_some_candidate_nondeterministically() {
        // Two functions named "run" in different files. An unqualified
        // call to "run" resolves via symbol_index, which is populated
        // by iterating an unordered HashMap -- which candidate wins is
        // unspecified and can differ between runs/builds.
        let mut structure = HashMap::new();
        structure.insert(
            "a.c".to_string(),
            filedata(vec![func("func_run::a.c", "run", vec![])], vec![]),
        );
        structure.insert(
            "b.c".to_string(),
            filedata(vec![func("func_run::b.c", "run", vec![])], vec![]),
        );
        structure.insert(
            "caller.c".to_string(),
            filedata(
                vec![func("func_caller::caller.c", "caller", vec!["run"])],
                vec![],
            ),
        );
        let g = build_call_graph_v2(&structure);
        let edge = g.edges.iter().find(|e| e.from == "func_caller::caller.c");
        assert!(
            edge.is_some(),
            "should resolve to *some* run — just not a guaranteed-stable one"
        );
    }

    #[test]
    fn call_to_nonexistent_function_produces_no_edge_and_no_panic() {
        let mut structure = HashMap::new();
        structure.insert(
            "a.c".to_string(),
            filedata(
                vec![func(
                    "func_caller::a.c",
                    "caller",
                    vec!["totally_missing_fn"],
                )],
                vec![],
            ),
        );
        let g = build_call_graph_v2(&structure);
        assert!(g.edges.is_empty());
        assert_eq!(g.nodes.len(), 1);
    }

    #[test]
    fn v1_par_chunks_boundary_at_exactly_chunk_size() {
        // CHUNK_SIZE = 2000 in build_call_graph; verify n-1, n, n+1 all
        // preserve exactly the right node count (off-by-one bugs in
        // manual chunking are a classic source of silently dropped data).
        for n in [1999usize, 2000, 2001] {
            let mut structure = HashMap::new();
            for i in 0..n {
                structure.insert(
                    format!("f{i}.c"),
                    filedata(
                        vec![func(
                            &format!("func_f{i}::f{i}.c"),
                            &format!("f{i}"),
                            vec![],
                        )],
                        vec![],
                    ),
                );
            }
            let g = build_call_graph(&structure);
            assert_eq!(
                g.nodes.len(),
                n,
                "chunk boundary n={n} lost or duplicated nodes"
            );
        }
    }

    #[test]
    fn inheritance_to_an_unregistered_base_class_is_skipped_not_panicked() {
        // Base class reference to something that was never parsed as a
        // node (external/third-party base) must not create a dangling
        // edge or panic.
        let mut structure = HashMap::new();
        let cls = Class {
            id: "class_Child::a.c".to_string(),
            name: "Child".to_string(),
            bases: vec!["ExternalLibBase".to_string()],
            ..Default::default()
        };
        structure.insert("a.c".to_string(), filedata(vec![], vec![cls]));
        let g = build_call_graph_v2(&structure);
        assert!(g.edges.iter().all(|e| e.edge_type != "inheritance"));
    }

    #[test]
    fn duplicate_calls_on_the_v2_path_are_deduped_per_source_node() {
        // v2 uses a `seen: HashSet<(from, to)>` per chunk, so calling the
        // same function twice from the same caller produces one edge,
        // not two -- verify that intentional behavior explicitly.
        let mut structure = HashMap::new();
        structure.insert(
            "a.c".to_string(),
            filedata(
                vec![func("func_caller::a.c", "caller", vec!["helper", "helper"])],
                vec![],
            ),
        );
        structure.insert(
            "b.c".to_string(),
            filedata(vec![func("func_helper::b.c", "helper", vec![])], vec![]),
        );
        let g = build_call_graph_v2(&structure);
        let count = g
            .edges
            .iter()
            .filter(|e| e.from == "func_caller::a.c" && e.to == "func_helper::b.c")
            .count();
        assert_eq!(
            count, 1,
            "v2's `seen` set collapses repeated calls to the same callee into one edge"
        );
    }

    fn lang_filedata(language: &str, functions: Vec<Function>) -> FileData {
        FileData {
            language: language.to_string(),
            functions,
            ..Default::default()
        }
    }

    #[test]
    fn v2_never_resolves_a_bare_name_into_another_language() {
        // A polyglot monorepo: `items.find()` in a .tsx component is recorded
        // as `find`; the only `find` in the project is a Python test helper.
        // Without a language guard the project-wide tier picks it.
        let mut structure = HashMap::new();
        structure.insert(
            "web/list.tsx".to_string(),
            lang_filedata(
                "typescript",
                vec![func("func_List::web/list.tsx", "List", vec!["find", "Row"])],
            ),
        );
        structure.insert(
            "web/row.tsx".to_string(),
            lang_filedata(
                "typescript",
                vec![func("func_Row::web/row.tsx", "Row", vec![])],
            ),
        );
        structure.insert(
            "tests/test_search.py".to_string(),
            lang_filedata(
                "python",
                vec![func("func_find::tests/test_search.py", "find", vec![])],
            ),
        );
        let g = build_call_graph_v2(&structure);
        let targets: Vec<&str> = g
            .edges
            .iter()
            .filter(|e| e.from == "func_List::web/list.tsx")
            .map(|e| e.to.as_str())
            .collect();
        assert_eq!(targets, vec!["func_Row::web/row.tsx"]);
    }

    // ───────────── import resolution: real parsers, then PRISM v2 ─────────────

    use crate::struc::kb_struct::CallGraph;
    use std::path::Path;

    fn project(files: &[(&str, &str)]) -> HashMap<String, FileData> {
        files
            .iter()
            .map(|(path, src)| {
                #[allow(clippy::expect_used)]
                let (p, fd) = crate::grammar_files::parse_source(Path::new(path), src)
                    .expect("fixture parses");
                (p, fd)
            })
            .collect()
    }

    /// `(callee id, resolution)` of every call edge out of `caller`, sorted.
    fn calls_of(g: &CallGraph, caller: &str) -> Vec<(String, String)> {
        let mut v: Vec<(String, String)> = g
            .edges
            .iter()
            .filter(|e| e.edge_type == "call" && e.from == caller)
            .map(|e| (e.to.clone(), e.resolution.clone()))
            .collect();
        v.sort();
        v
    }

    fn edge(to: &str, how: &str) -> (String, String) {
        (to.to_string(), how.to_string())
    }

    const KNF: &str = "func_read_page::packages/providers/src/kyc_providers/adapters/knf.py";
    const PK: &str = "func_read_page::packages/providers/src/kyc_providers/adapters/pk.py";
    const REGISTERS: &str =
        "func_company_registers::packages/providers/src/kyc_providers/registry.py";

    /// Two adapters of a src-layout package both define `read_page`; every
    /// caller reaches the one its file imports, however it imports it.
    fn python_project() -> HashMap<String, FileData> {
        project(&[
            (
                "packages/providers/src/kyc_providers/__init__.py",
                "from .registry import company_registers\n",
            ),
            (
                "packages/providers/src/kyc_providers/registry.py",
                "def company_registers(code):\n    return ()\n",
            ),
            ("packages/providers/src/kyc_providers/adapters/__init__.py", ""),
            (
                "packages/providers/src/kyc_providers/adapters/knf.py",
                "def read_page(html):\n    return []\n\n\
                 class Knf:\n    def _read(self, html):\n        return read_page(html)\n",
            ),
            (
                "packages/providers/src/kyc_providers/adapters/pk.py",
                "def read_page(html):\n    return []\n",
            ),
            (
                "packages/providers/src/kyc_providers/adapters/both.py",
                "from . import knf\nfrom .pk import read_page\nfrom ..registry import company_registers\n\n\
                 def relative(html):\n    knf.read_page(html)\n    read_page(html)\n    company_registers('PK')\n",
            ),
            (
                "tests/test_pk.py",
                "import kyc_providers.adapters.pk\n\
                 import kyc_providers.adapters.knf as knf_mod\n\
                 from kyc_providers import company_registers\n\
                 from kyc_providers.adapters import knf\n\
                 from kyc_providers.adapters.knf import read_page as read_knf\n\
                 from kyc_providers.adapters.pk import (\n    SITE,\n    read_page,\n)\n\n\
                 def test_named():\n    read_page('')\n\n\
                 def test_renamed():\n    read_knf('')\n\n\
                 def test_module_alias():\n    knf_mod.read_page('')\n\n\
                 def test_submodule():\n    knf.read_page('')\n\n\
                 def test_dotted():\n    kyc_providers.adapters.pk.read_page('')\n\n\
                 def test_reexported():\n    company_registers('PK')\n",
            ),
            (
                "tests/test_loose.py",
                "def test_unimported():\n    read_page('')\n    company_registers('PK')\n\n\
                 def test_receiver(page):\n    page.read_page()\n",
            ),
        ])
    }

    #[test]
    fn python_calls_resolve_through_the_callers_imports() {
        let g = build_call_graph_v2(&python_project());
        let t = |name: &str| calls_of(&g, &format!("func_{name}::tests/test_pk.py"));
        assert_eq!(t("test_named"), vec![edge(PK, "import")]);
        assert_eq!(t("test_renamed"), vec![edge(KNF, "import")]);
        assert_eq!(t("test_module_alias"), vec![edge(KNF, "import")]);
        assert_eq!(t("test_submodule"), vec![edge(KNF, "import")]);
        assert_eq!(t("test_dotted"), vec![edge(PK, "import")]);
        // `from kyc_providers import company_registers` reaches the def in
        // registry.py through the package's `__init__.py` re-export.
        assert_eq!(t("test_reexported"), vec![edge(REGISTERS, "import")]);
    }

    #[test]
    fn python_relative_imports_and_same_file_calls() {
        let g = build_call_graph_v2(&python_project());
        assert_eq!(
            calls_of(
                &g,
                "func_relative::packages/providers/src/kyc_providers/adapters/both.py"
            ),
            vec![
                edge(REGISTERS, "import"),
                edge(KNF, "import"),
                edge(PK, "import"),
            ]
        );
        assert_eq!(
            calls_of(
                &g,
                "method_Knf__read::packages/providers/src/kyc_providers/adapters/knf.py"
            ),
            vec![edge(KNF, "local")]
        );
    }

    #[test]
    fn python_unimported_name_is_ambiguous_not_silently_picked() {
        let g = build_call_graph_v2(&python_project());
        // Two `read_page`s and no import: both, flagged; one
        // `company_registers`: a by-name edge, flagged as such.
        assert_eq!(
            calls_of(&g, "func_test_unimported::tests/test_loose.py"),
            vec![
                edge(REGISTERS, "name"),
                edge(KNF, "ambiguous"),
                edge(PK, "ambiguous"),
            ]
        );
        // `page.read_page()` is a method of whatever `page` is, never one of
        // the module-level functions.
        assert!(calls_of(&g, "func_test_receiver::tests/test_loose.py").is_empty());
        // By-name guesses do not count as traffic.
        let pk = g
            .nodes
            .iter()
            .find(|n| n.id == PK)
            .map(|n| n.call_count_estimate);
        assert_eq!(pk, Some(3), "test_named, test_dotted, relative");
    }

    const WEB_A: &str = "func_format::apps/web/src/lib/a.ts";
    const WEB_B: &str = "func_format::apps/web/src/lib/b.ts";
    const MOBILE_A: &str = "func_format::apps/mobile/src/lib/a.ts";

    fn ts_project() -> HashMap<String, FileData> {
        project(&[
            (
                "apps/web/src/lib/a.ts",
                "export function format(x: number) { return ''; }\n",
            ),
            (
                "apps/web/src/lib/b.ts",
                "export function format(x: number) { return ''; }\n",
            ),
            (
                "apps/web/src/lib/index.ts",
                "export { format as formatB } from './b';\n",
            ),
            (
                "apps/mobile/src/lib/a.ts",
                "export function format(x: number) { return ''; }\n",
            ),
            (
                "apps/web/src/components/view.tsx",
                "import { format } from '@/lib/a';\n\
                 import { format as fmtB } from '../lib/b';\n\
                 import * as libB from '@/lib/b';\n\
                 import { formatB } from '@/lib';\n\
                 export function Named() { return format(1); }\n\
                 export function Renamed() { return fmtB(1); }\n\
                 export function Namespace() { return libB.format(1); }\n\
                 export function Barrel() { return formatB(1); }\n",
            ),
            (
                "apps/mobile/src/screens/home.tsx",
                "import { format } from '@/lib/a';\n\
                 export function Home() { return format(1); }\n",
            ),
            (
                "apps/web/src/components/loose.ts",
                "export function Loose(items: string[]) { items.format(); return format(1); }\n",
            ),
        ])
    }

    #[test]
    fn ts_calls_resolve_through_relative_alias_namespace_and_barrel_imports() {
        let g = build_call_graph_v2(&ts_project());
        let v = |name: &str| {
            calls_of(
                &g,
                &format!("func_{name}::apps/web/src/components/view.tsx"),
            )
        };
        assert_eq!(v("Named"), vec![edge(WEB_A, "import")]);
        assert_eq!(v("Renamed"), vec![edge(WEB_B, "import")]);
        assert_eq!(v("Namespace"), vec![edge(WEB_B, "import")]);
        assert_eq!(v("Barrel"), vec![edge(WEB_B, "import")]);
        // `@/` is the importing file's own app: mobile's `@/lib/a` is mobile's.
        assert_eq!(
            calls_of(&g, "func_Home::apps/mobile/src/screens/home.tsx"),
            vec![edge(MOBILE_A, "import")]
        );
    }

    #[test]
    fn ts_receiver_call_keeps_its_qualifier_and_unimported_name_is_ambiguous() {
        let fd = &ts_project()["apps/web/src/components/loose.ts"];
        let callees: Vec<&str> = fd.functions[0]
            .calls
            .iter()
            .map(|c| c.callee.as_str())
            .collect();
        assert_eq!(callees, vec!["items.format", "format"]);

        let g = build_call_graph_v2(&ts_project());
        assert_eq!(
            calls_of(&g, "func_Loose::apps/web/src/components/loose.ts"),
            vec![
                edge(MOBILE_A, "ambiguous"),
                edge(WEB_A, "ambiguous"),
                edge(WEB_B, "ambiguous"),
            ]
        );
    }
}

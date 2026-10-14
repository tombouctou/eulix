// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

package query

import (
	"encoding/json"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"eulix/internal/utils"
)

func endpoint(path, function, file string, line int, methods ...string) utils.EntryPoint {
	p := path
	return utils.EntryPoint{
		EntryType: "api_endpoint", Path: &p, Function: function,
		Handler: "method_" + strings.ReplaceAll(function, ".", "_") + "::" + file,
		File:    file, Line: line, Methods: methods,
	}
}

const issuesCs = "src/Pm.Api/Controllers/IssuesController.cs"

func routeFixture() []utils.EntryPoint {
	return []utils.EntryPoint{
		endpoint("rest/api/2/issue/{idOrKey}/transitions", "IssuesController.GetTransitions", issuesCs, 674, "GET"),
		endpoint("rest/api/2/issue/{idOrKey}/transitions", "IssuesController.DoTransition", issuesCs, 769, "POST"),
		endpoint("rest/api/2/issue/{idOrKey}", "IssuesController.GetIssue", issuesCs, 120, "GET"),
		endpoint("rest/api/2/workflow/transitions/{id:int}", "WorkflowController.Rule", "src/W.cs", 30, "GET"),
		endpoint("api/[controller]/{id?}", "BoardsController.Get", "src/B.cs", 10, "GET"),
		endpoint("/files/{*path}", "files_get", "app/files.py", 5, "GET"),
		endpoint("/invoices", "list_invoices", "app/billing.py", 262, "GET"),
	}
}

// writeRoutes puts eps where the router reads them, and returns the router.
func writeRoutes(t *testing.T, eps []utils.EntryPoint) *Router {
	t.Helper()
	r := newRouter(t)
	data, err := json.Marshal(utils.EntryPointsRef{EntryPoints: eps})
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(r.eulixDir, "kb_entry_points.json"), data, 0o644); err != nil {
		t.Fatal(err)
	}
	return r
}

func TestParseRouteQuery(t *testing.T) {
	cases := []struct {
		q      string
		ok     bool
		method string
		segs   []string
		words  []string
	}{
		{"POST rest/api/2/issue/{idOrKey}/transitions", true, "POST", []string{"rest", "api", "2", "issue", "{idOrKey}", "transitions"}, nil},
		{"/rest/api/2/issue/KYC-1/transitions", true, "", []string{"rest", "api", "2", "issue", "KYC-1", "transitions"}, nil},
		{"post `/rest/api/2/issue/KYC-1/transitions`?", true, "POST", []string{"rest", "api", "2", "issue", "KYC-1", "transitions"}, nil},
		{"https://pm.example.com/rest/api/2/issue/KYC-1?expand=names", true, "", []string{"rest", "api", "2", "issue", "KYC-1"}, nil},
		{"GET /invoices", true, "GET", []string{"invoices"}, nil},
		{"transitions endpoint", true, "", nil, []string{"transitions"}},
		{"which endpoint handles transitions", true, "", nil, []string{"transitions"}},
		{"POST transitions route", true, "POST", nil, []string{"transitions"}},
		{"what is the transitions endpoint  Key symbols: idOrKey, Foo", true, "", nil, []string{"transitions"}},
		// Not route lookups: a source path, prose with a slash, a question
		// without a route word, or too many words for a lookup.
		{"src/Pm.Api/Controllers/IssuesController.cs", false, "", nil, nil},
		{"read and/or write", false, "", nil, nil},
		{"what is {id}", false, "", nil, nil},
		{"how are transitions validated", false, "", nil, nil},
		{"how does the transitions endpoint check permissions and statuses of the issue", false, "", nil, nil},
	}
	for _, c := range cases {
		rq, ok := parseRouteQuery(c.q)
		if ok != c.ok || rq.method != c.method || !reflect.DeepEqual(rq.segs, c.segs) || !reflect.DeepEqual(rq.words, c.words) {
			t.Errorf("%q: got ok=%v %+v", c.q, ok, rq)
		}
	}
}

func TestFindRoutes(t *testing.T) {
	routes := compileRoutes(routeFixture())
	find := func(q string) []string {
		t.Helper()
		rq, ok := parseRouteQuery(q)
		if !ok {
			t.Fatalf("%q is not a route query", q)
		}
		hits, _ := findRoutes(rq, routes)
		var out []string
		for _, h := range hits {
			out = append(out, h.re.ep.Function)
		}
		return out
	}
	cases := []struct {
		q    string
		want []string
	}{
		// Template with placeholder, method picks one of two actions.
		{"POST rest/api/2/issue/{idOrKey}/transitions", []string{"IssuesController.DoTransition"}},
		// A concrete key fills the parameter; no method: both actions.
		{"/rest/api/2/issue/KYC-1/transitions", []string{"IssuesController.DoTransition", "IssuesController.GetTransitions"}},
		// A placeholder never stands for a literal segment.
		{"GET rest/api/2/issue/{key}", []string{"IssuesController.GetIssue"}},
		// `{id:int}` constraint, `[controller]`, optional and catch-all parameters.
		{"GET /rest/api/2/workflow/transitions/7", []string{"WorkflowController.Rule"}},
		{"GET /api/Boards", []string{"BoardsController.Get"}},
		{"/api/boards/3", []string{"BoardsController.Get"}},
		{"/files/a/b/c.txt", []string{"files_get"}},
		// A router mounted under a prefix the template does not carry.
		{"GET /api/billing/invoices", []string{"list_invoices"}},
		{"GET /invoices", []string{"list_invoices"}},
		// A tail of the template.
		{"issue/{idOrKey}/transitions endpoint", []string{"IssuesController.DoTransition", "IssuesController.GetTransitions"}},
		// Words: literal segments first, then segments containing the word.
		{"transitions endpoint", []string{"IssuesController.DoTransition", "IssuesController.GetTransitions", "WorkflowController.Rule"}},
		{"POST transitions endpoint", []string{"IssuesController.DoTransition"}},
		{"/nothing/like/this", nil},
	}
	for _, c := range cases {
		if got := find(c.q); !reflect.DeepEqual(got, c.want) {
			t.Errorf("%q: got %v, want %v", c.q, got, c.want)
		}
	}
	// A method no endpoint of that path has: the others, flagged.
	rq, _ := parseRouteQuery("DELETE /rest/api/2/issue/KYC-1/transitions")
	hits, other := findRoutes(rq, routes)
	if !other || len(hits) != 2 {
		t.Errorf("DELETE: other=%v hits=%d", other, len(hits))
	}
}

func TestRouteLookup(t *testing.T) {
	const do = "method_IssuesController_DoTransition::" + issuesCs
	r := writeRoutes(t, routeFixture())
	r.setGraph(t, M{
		"Nodes": S{
			node(do, issuesCs, "method", 0),
			node("method_IssueTransition_MoveAsync::src/T.cs", "src/T.cs", "method", 1),
		},
		"Edges": S{edge(do, "method_IssueTransition_MoveAsync::src/T.cs")},
	})

	text, direct := r.routeLookup("POST /rest/api/2/issue/{idOrKey}/transitions")
	want := lines(
		"API endpoints matching POST /rest/api/2/issue/{idOrKey}/transitions (from the route templates):",
		"  [POST] rest/api/2/issue/{idOrKey}/transitions → IssuesController.DoTransition  ("+issuesCs+":769)",
		"",
		"Handler:",
		"Call Graph: IssuesController.DoTransition",
		"  File    : "+issuesCs,
		"  Type    : method",
		"  Metrics : Fan-in 0 | Fan-out 1",
		"",
		"┌── Called by (Inbound):",
		"│   (none — likely an entry point or exported API)",
		"└── Calls (Outbound):",
		"    → IssueTransition.MoveAsync",
	)
	if !direct || text != want {
		t.Errorf("direct=%v got:\n%s\nwant:\n%s", direct, text, want)
	}

	// The router answers it before classifying, in both entry points.
	for name, run := range map[string]func(string) (string, error){
		"PromptOrAnswerWithCoT": func(q string) (string, error) { return r.PromptOrAnswerWithCoT(q, false) },
		"QueryEngine":           r.QueryEngine,
	} {
		got, err := run("transitions endpoint")
		if err != nil || !strings.Contains(got, "→ IssuesController.DoTransition") ||
			!strings.Contains(got, "→ IssuesController.GetTransitions") {
			t.Errorf("%s: err=%v got:\n%s", name, err, got)
		}
	}

	// A question about a route is not a lookup: the endpoints are a preface
	// to its context, without the handler's graph.
	text, direct = r.routeLookup("why does POST /rest/api/2/issue/KYC-1/transitions refuse a move into a done status for a member")
	if direct || !strings.HasPrefix(text, "API endpoints matching POST") || strings.Contains(text, "Handler:") {
		t.Errorf("direct=%v got:\n%s", direct, text)
	}

	// No entry points file, or nothing matching: no answer.
	if text, direct := newRouter(t).routeLookup("transitions endpoint"); text != "" || direct {
		t.Errorf("without entry points: %q %v", text, direct)
	}
	if text, direct := r.routeLookup("/nothing/like/this"); text != "" || direct {
		t.Errorf("no match: %q %v", text, direct)
	}
}

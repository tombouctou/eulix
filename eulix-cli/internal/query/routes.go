// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

package query

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"

	"eulix/internal/utils"
)

// ========== Route lookup ==========
//
// A query naming an HTTP route — `POST rest/api/2/issue/{idOrKey}/transitions`,
// `/rest/api/2/issue/KYC-1/transitions`, `transitions endpoint` — is answered
// from the api_endpoint entry points (kb_entry_points.json) before anything
// else: the route template is the one place the handler is tied to the URL,
// and a lexical or semantic search over the source rarely finds it.

// maxRouteHits caps how many matching endpoints one answer lists.
const maxRouteHits = 10

// maxRouteWords is the longest words-only query (`transitions endpoint`)
// that is still a route lookup rather than a question about the code.
const maxRouteWords = 6

var (
	httpMethods = map[string]bool{
		"GET": true, "POST": true, "PUT": true, "PATCH": true, "DELETE": true, "HEAD": true, "OPTIONS": true,
	}
	// reRouteToken is a path-shaped token: segments of URL characters and
	// `{param}` placeholders, with at least one slash (`/invoices` too).
	reRouteToken = regexp.MustCompile(`^/?[\w\-.~:{}*?\[\]%@!$&'()+,;=]+(?:/[\w\-.~:{}*?\[\]%@!$&'()+,;=]*)*$`)
	// reSourceFile rules out a file path (`src/a/b.cs`) taken for a route.
	reSourceFile = regexp.MustCompile(`\.(?:go|py|js|jsx|ts|tsx|java|rs|rb|php|cs|kt|swift|scala|c|cc|cpp|h|hpp|sh|sql|md|json|ya?ml|toml|html|css)$`)
	reRouteParam = regexp.MustCompile(`\{[^}]*\}`)
	// routeKeywords mark a words-only query as a route lookup.
	routeKeywords = map[string]bool{
		"endpoint": true, "endpoints": true, "route": true, "routes": true, "url": true, "urls": true,
	}
	// routeFiller words carry nothing to match a route by.
	routeFiller = map[string]bool{
		"the": true, "a": true, "an": true, "for": true, "of": true, "to": true, "is": true, "which": true,
		"what": true, "where": true, "who": true, "handles": true, "handler": true, "serves": true,
		"find": true, "show": true, "api": true, "http": true, "path": true, "controller": true,
		"action": true, "in": true, "on": true, "me": true, "list": true,
	}
)

// routeQuery is what a query asks of the routes: an HTTP method (optional)
// and either a path (segments) or a few words.
type routeQuery struct {
	method string
	path   string
	segs   []string
	words  []string
	// other words of a query with a path: more than maxRouteWords make it
	// a question about the endpoint rather than a lookup of it.
	extra int
}

// parseRouteQuery reports whether q is a route lookup, and of what. A
// "Key symbols: ..." tail the MCP cascade appends is ignored.
func parseRouteQuery(q string) (routeQuery, bool) {
	if i := strings.Index(q, "Key symbols:"); i >= 0 {
		q = q[:i]
	}
	var rq routeQuery
	var rest []string
	keyword := false
	for _, raw := range strings.Fields(q) {
		tok := strings.TrimRight(strings.Trim(raw, "`'\",;()<>"), ".?!:")
		tok = strings.TrimRight(strings.Trim(tok, "`'\",;()<>"), ".?!:")
		if tok == "" {
			continue
		}
		if httpMethods[tok] || (httpMethods[strings.ToUpper(tok)] && rq.method == "" && len(rest) == 0 && rq.path == "") {
			if rq.method == "" {
				rq.method = strings.ToUpper(tok)
			}
			continue
		}
		if rq.path == "" {
			if p, ok := routePath(tok); ok {
				rq.path = p
				continue
			}
		}
		low := strings.ToLower(tok)
		if routeKeywords[low] {
			keyword = true
			continue
		}
		rest = append(rest, low)
	}
	if rq.path != "" {
		rq.segs = splitRoute(rq.path)
		for _, w := range rest {
			if !routeFiller[w] {
				rq.extra++
			}
		}
		return rq, len(rq.segs) > 0
	}
	if !keyword || len(rest) == 0 || len(rest) > maxRouteWords {
		return routeQuery{}, false
	}
	for _, w := range rest {
		if !routeFiller[w] {
			rq.words = append(rq.words, w)
		}
	}
	return rq, len(rq.words) > 0
}

// routePath returns tok as a URL path, scheme, host and query string
// dropped, if it looks like one.
func routePath(tok string) (string, bool) {
	if i := strings.Index(tok, "://"); i >= 0 {
		rest := tok[i+3:]
		j := strings.IndexByte(rest, '/')
		if j < 0 {
			return "", false
		}
		tok = rest[j:]
	}
	if i := strings.IndexAny(tok, "?#"); i > 0 && !strings.Contains(tok[i:], "}") {
		tok = tok[:i]
	}
	if !strings.Contains(tok, "/") || !reRouteToken.MatchString(tok) ||
		reSourceFile.MatchString(strings.ToLower(tok)) {
		return "", false
	}
	// `a/b` alone is as likely prose ("and/or") as a route: a route either
	// starts with a slash or has three segments, or a placeholder.
	if !strings.HasPrefix(tok, "/") && strings.Count(tok, "/") < 2 && !strings.Contains(tok, "{") {
		return "", false
	}
	return tok, true
}

func splitRoute(p string) []string {
	var out []string
	for _, s := range strings.Split(p, "/") {
		if s != "" {
			out = append(out, s)
		}
	}
	return out
}

// routeEntry is an api_endpoint entry point with its template compiled.
type routeEntry struct {
	ep   utils.EntryPoint
	path string
	segs []routeSeg
}

type routeSeg struct {
	literal  string         // lower-cased; "" for a parameter segment
	re       *regexp.Regexp // a segment mixing text and `{param}` (`v{version}`)
	param    bool
	optional bool // `{id?}`, `{id=1}`
	rest     bool // catch-all `{*path}`
}

// compileRoute turns a route template into segments. ASP.NET's
// `[controller]` / `[action]` become the controller / action name.
func compileRoute(ep utils.EntryPoint) routeEntry {
	path := *ep.Path
	if ctl, act, ok := strings.Cut(ep.Function, "."); ok {
		ctl = strings.TrimSuffix(ctl, "Controller")
		path = strings.ReplaceAll(path, "[controller]", ctl)
		path = strings.ReplaceAll(path, "[action]", act)
	}
	re := routeEntry{ep: ep, path: path}
	for _, s := range splitRoute(path) {
		var seg routeSeg
		switch {
		case strings.HasPrefix(s, "{") && strings.HasSuffix(s, "}") && strings.Count(s, "{") == 1:
			inner := s[1 : len(s)-1]
			seg.param = true
			seg.rest = strings.HasPrefix(inner, "*")
			seg.optional = strings.HasSuffix(inner, "?") || strings.Contains(inner, "=")
		case strings.Contains(s, "{"):
			parts := reRouteParam.Split(s, -1)
			for i, p := range parts {
				parts[i] = regexp.QuoteMeta(p)
			}
			seg.re = regexp.MustCompile(`(?i)^` + strings.Join(parts, `[^/]+`) + `$`)
		default:
			seg.literal = strings.ToLower(s)
		}
		re.segs = append(re.segs, seg)
	}
	return re
}

// matchSegs reports whether query segments q match template segments t in
// full, and how many literal segments agreed (the specificity).
func matchSegs(q []string, t []routeSeg) (int, bool) {
	lits := 0
	i := 0
	for j, seg := range t {
		if seg.rest {
			return lits, true
		}
		if i >= len(q) {
			// Only optional parameters may be left over.
			for _, s := range t[j:] {
				if !s.optional && !s.rest {
					return 0, false
				}
			}
			return lits, true
		}
		qs := q[i]
		isPlaceholder := strings.HasPrefix(qs, "{") && strings.HasSuffix(qs, "}")
		switch {
		case seg.param:
			// a parameter takes any value, or a placeholder
		case isPlaceholder:
			if seg.re == nil {
				return 0, false
			}
		case seg.re != nil:
			if !seg.re.MatchString(qs) {
				return 0, false
			}
		default:
			if strings.ToLower(qs) != seg.literal {
				return 0, false
			}
			lits++
		}
		i++
	}
	return lits, i == len(q)
}

// routeHit is one endpoint matching a query, ranked by score.
type routeHit struct {
	re    *routeEntry
	score int
	note  string
}

// matchRoute scores one endpoint against the query; 0 = no match.
//
// A path matches the whole template best; a query path longer than the
// template may carry a prefix the template does not (a router mounted
// under `/api`, a base path), and a shorter one may be the template's
// tail (`issue/{id}/transitions`) — both rank lower.
func matchRoute(rq routeQuery, re *routeEntry) (int, string) {
	if len(rq.segs) > 0 {
		if lits, ok := matchSegs(rq.segs, re.segs); ok {
			return 1000 + lits, ""
		}
		for skip := 1; skip < len(rq.segs); skip++ {
			if lits, ok := matchSegs(rq.segs[skip:], re.segs); ok && lits > 0 {
				return 500 + lits - skip, "template is a tail of the path"
			}
		}
		if len(rq.segs) < len(re.segs) {
			for skip := 1; skip < len(re.segs); skip++ {
				tail := re.segs[skip:]
				if lits, ok := matchSegs(rq.segs, tail); ok && lits > 0 {
					return 400 + lits - skip, "path is a tail of the template"
				}
			}
		}
		return 0, ""
	}
	// Words: each must be a literal segment of the template, or a part of
	// one or of the handler's name.
	handler := strings.ToLower(re.ep.Function)
	score := 0
	for _, w := range rq.words {
		best := 0
		for _, s := range re.segs {
			switch {
			case s.literal == w:
				best = max(best, 3)
			case s.literal != "" && strings.Contains(s.literal, w):
				best = max(best, 2)
			}
		}
		if best == 0 && strings.Contains(handler, w) {
			best = 1
		}
		if best == 0 {
			return 0, ""
		}
		score += best
	}
	return score, ""
}

// loadRoutes reads the api_endpoint entry points that carry a path, once.
func (r *Router) loadRoutes() []routeEntry {
	r.routesOnce.Do(func() {
		data, err := os.ReadFile(filepath.Join(r.eulixDir, "kb_entry_points.json"))
		if err != nil {
			return
		}
		var ref utils.EntryPointsRef
		if json.Unmarshal(data, &ref) != nil {
			return
		}
		r.routes = compileRoutes(ref.EntryPoints)
	})
	return r.routes
}

func compileRoutes(eps []utils.EntryPoint) []routeEntry {
	var out []routeEntry
	for _, ep := range eps {
		if ep.EntryType != "api_endpoint" || ep.Path == nil || strings.TrimSpace(*ep.Path) == "" {
			continue
		}
		out = append(out, compileRoute(ep))
	}
	return out
}

func hasMethod(ep utils.EntryPoint, m string) bool {
	if len(ep.Methods) == 0 {
		return true
	}
	for _, x := range ep.Methods {
		if strings.EqualFold(x, m) || x == "*" {
			return true
		}
	}
	return false
}

// findRoutes returns the endpoints matching rq, best first. With a method
// given, endpoints of other methods are dropped — unless none is left,
// then they are returned with otherMethods set.
func findRoutes(rq routeQuery, routes []routeEntry) (hits []routeHit, otherMethods bool) {
	var all []routeHit
	for i := range routes {
		if s, note := matchRoute(rq, &routes[i]); s > 0 {
			all = append(all, routeHit{re: &routes[i], score: s, note: note})
		}
	}
	if rq.method != "" {
		for _, h := range all {
			if hasMethod(h.re.ep, rq.method) {
				hits = append(hits, h)
			}
		}
		if len(hits) == 0 && len(all) > 0 {
			hits, otherMethods = all, true
		}
	} else {
		hits = all
	}
	sort.SliceStable(hits, func(i, j int) bool {
		if hits[i].score != hits[j].score {
			return hits[i].score > hits[j].score
		}
		if hits[i].re.path != hits[j].re.path {
			return hits[i].re.path < hits[j].re.path
		}
		return hits[i].re.ep.Function < hits[j].re.ep.Function
	})
	// A full-path match makes the partial ones noise.
	if len(hits) > 0 && hits[0].score >= 1000 {
		n := 0
		for n < len(hits) && hits[n].score >= 1000 {
			n++
		}
		hits = hits[:n]
	}
	if len(hits) > maxRouteHits {
		hits = hits[:maxRouteHits]
	}
	return hits, otherMethods
}

// routeLookup answers a route lookup from the entry points: the matching
// endpoints and, when one stands out, its handler's call graph. text is
// empty when q names no route or nothing matches. direct reports a query
// that is the lookup and nothing else — the text is the whole answer; a
// longer question about a route gets the text as a preface to its context.
func (r *Router) routeLookup(q string) (text string, direct bool) {
	rq, ok := parseRouteQuery(q)
	if !ok {
		return "", false
	}
	direct = rq.extra <= maxRouteWords
	routes := r.loadRoutes()
	if len(routes) == 0 {
		return "", false
	}
	hits, otherMethods := findRoutes(rq, routes)
	if len(hits) == 0 {
		return "", false
	}
	asked := rq.path
	if asked == "" {
		asked = strings.Join(rq.words, " ")
	}
	if rq.method != "" {
		asked = rq.method + " " + asked
	}

	var b strings.Builder
	fmt.Fprintf(&b, "API endpoints matching %s (from the route templates):\n", asked)
	if otherMethods {
		fmt.Fprintf(&b, "  (no %s endpoint has this path; other methods:)\n", rq.method)
	}
	for _, h := range hits {
		ep := h.re.ep
		methods := strings.Join(ep.Methods, ", ")
		if methods == "" {
			methods = "ANY"
		}
		fmt.Fprintf(&b, "  [%s] %s → %s  (%s:%d)", methods, *ep.Path, ep.Function, ep.File, ep.Line)
		if h.note != "" {
			fmt.Fprintf(&b, "  — %s", h.note)
		}
		b.WriteString("\n")
	}
	if direct && (len(hits) == 1 || hits[0].score > hits[1].score) {
		if key, node := r.routeHandlerNode(hits[0].re.ep); node != nil {
			b.WriteString("\nHandler:\n")
			b.WriteString(r.callGraphBody(key, node))
		}
	}
	return b.String(), direct
}

// RouteLookup is routeLookup for the MCP server, which runs it ahead of
// its retrieval cascade.
func (r *Router) RouteLookup(q string) (string, bool) {
	return r.routeLookup(q)
}

// routeHandlerNode finds the call graph node of an endpoint's handler: the
// handler is the node id for C#, a bare function name elsewhere.
func (r *Router) routeHandlerNode(ep utils.EntryPoint) (string, *utils.CallGraphNode) {
	if r.cgBuild == nil {
		return "", nil
	}
	for _, k := range []string{
		ep.Handler,
		"func_" + ep.Handler + "::" + ep.File,
		"method_" + strings.ReplaceAll(ep.Function, ".", "_") + "::" + ep.File,
	} {
		if n, ok := r.cgBuild.Nodes[k]; ok {
			return k, n
		}
	}
	return "", nil
}

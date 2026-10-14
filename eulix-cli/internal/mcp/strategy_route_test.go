// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

package mcp

import (
	"context"
	"strings"
	"testing"
)

// stubRetriever answers every retrieval stage with fixed text and counts
// the calls; Route answers only `route`.
type stubRetriever struct {
	route string
	text  string
	calls int
}

func (s *stubRetriever) OpenEnded(context.Context, string, bool) (string, error) {
	s.calls++
	return s.text, nil
}

func (s *stubRetriever) Anchored(context.Context, string, []string, bool) (string, error) {
	s.calls++
	return s.text, nil
}

func (s *stubRetriever) MultiHop(context.Context, string, []string, []string, bool) (string, error) {
	s.calls++
	return s.text, nil
}

func (s *stubRetriever) Route(q string) (string, bool) {
	if q == s.route {
		return "API endpoints matching " + q + ":\n  [POST] x → C.Do  (C.cs:1)\n", true
	}
	return "", false
}

func TestRouteStageRunsFirstAndAlone(t *testing.T) {
	stub := &stubRetriever{
		route: "/rest/api/2/issue/KYC-1/transitions",
		text:  strings.Repeat("unrelated retrieval text ", 20),
	}
	s := &Server{strategy: DefaultStrategyConfig(), retriever: stub}

	// A bare URL scores poorly by words and anchors; the route stage is
	// not scored, and nothing else runs.
	got, trace, err := s.retrieveLocked(context.Background(), stub.route, nil, false)
	if err != nil || !strings.Contains(got, "C.Do") || trace.Chosen != StageRoute || stub.calls != 0 {
		t.Fatalf("err=%v chosen=%s calls=%d got=%q", err, trace.Chosen, stub.calls, got)
	}

	// Any other query goes down the usual cascade.
	_, trace, _ = s.retrieveLocked(context.Background(), "how are transitions checked", nil, false)
	if trace.Chosen == StageRoute || stub.calls == 0 {
		t.Fatalf("chosen=%s calls=%d", trace.Chosen, stub.calls)
	}
}

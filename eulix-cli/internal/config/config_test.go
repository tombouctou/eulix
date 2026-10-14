// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

package config

import (
	"os"
	"path/filepath"
	"testing"
)

func TestEmbeddingsEnabledByDefault(t *testing.T) {
	t.Setenv(NoEmbeddingsEnv, "")
	cfg, err := LoadFrom(t.TempDir())
	if err != nil {
		t.Fatalf("LoadFrom: %v", err)
	}
	if !cfg.Embeddings.Enabled {
		t.Fatal("embeddings should be enabled when eulix.toml does not mention them")
	}
}

func TestEmbeddingsDisabledInToml(t *testing.T) {
	t.Setenv(NoEmbeddingsEnv, "")
	dir := t.TempDir()
	toml := "[embeddings]\nenabled = false\n"
	if err := os.WriteFile(filepath.Join(dir, "eulix.toml"), []byte(toml), 0o644); err != nil {
		t.Fatal(err)
	}
	cfg, err := LoadFrom(dir)
	if err != nil {
		t.Fatalf("LoadFrom: %v", err)
	}
	if cfg.Embeddings.Enabled {
		t.Fatal("[embeddings] enabled = false was ignored")
	}
	// The rest of the section keeps its defaults.
	if cfg.Embeddings.Model == "" {
		t.Fatal("model default lost when only `enabled` is set")
	}
}

func TestNoEmbeddingsEnvOverridesToml(t *testing.T) {
	for _, v := range []string{"1", "true", "YES", " on "} {
		t.Run(v, func(t *testing.T) {
			t.Setenv(NoEmbeddingsEnv, v)
			dir := t.TempDir()
			toml := "[embeddings]\nenabled = true\n"
			if err := os.WriteFile(filepath.Join(dir, "eulix.toml"), []byte(toml), 0o644); err != nil {
				t.Fatal(err)
			}
			cfg, err := LoadFrom(dir)
			if err != nil {
				t.Fatalf("LoadFrom: %v", err)
			}
			if cfg.Embeddings.Enabled {
				t.Fatalf("%s=%q should disable embeddings", NoEmbeddingsEnv, v)
			}
		})
	}
	t.Setenv(NoEmbeddingsEnv, "0")
	if NoEmbeddingsFromEnv() {
		t.Fatal(`"0" must not disable embeddings`)
	}
}

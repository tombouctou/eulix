// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

package utils

import (
	"fmt"
	"os"
	"path/filepath"
)

// EulixHomeEnv names the environment variable that relocates the global
// eulix directory (extracted parser, embed scripts, venv). Useful for
// sandboxes, CI and side-by-side installs where $HOME must stay untouched.
const EulixHomeEnv = "EULIX_HOME"

// GlobalRoot returns the global eulix directory without creating it:
// $EULIX_HOME when set, $HOME/.Eulix otherwise.
func GlobalRoot() (string, error) {
	if dir := os.Getenv(EulixHomeEnv); dir != "" {
		abs, err := filepath.Abs(dir)
		if err != nil {
			return "", fmt.Errorf("resolve %s=%q: %w", EulixHomeEnv, dir, err)
		}
		return abs, nil
	}
	homeDir, err := os.UserHomeDir()
	if err != nil {
		return "", fmt.Errorf("could not determine home directory: %w", err)
	}
	return filepath.Join(homeDir, EulixGlobalDir), nil
}

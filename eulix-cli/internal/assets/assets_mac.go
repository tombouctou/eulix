// Copyright 2025-2026 Dawood K. (Nurysso)
// SPDX-License-Identifier: Apache-2.0

// Package utils provides Shared type and func across project

//go:build darwin

package assets

import "embed"

// parserBin holds the macOS (Mach-O) eulix_parser binary. Only compiled
// into darwin builds. this bin was build using cargo zigbuild --release --target aarch64-apple-darwin
// so may not work perfectly
//
//go:embed bins/eulix_parser_darwin
var parserBin embed.FS

const (
	parserBinFile     = "bins/eulix_parser_darwin"
	parserBinDestName = "eulix_parser"
)

// onnxruntime-rocm (onnx-amd.txt, the cross-platform default) ships no
// macOS wheels, so a darwin build that was not given a requirements file
// via -ldflags uses plain onnxruntime (CPU + CoreML execution providers).
func init() {
	if embed_requirements == "onnx-amd.txt" {
		embed_requirements = "onnx-mac.txt"
	}
}

func parserBinaryBytes() ([]byte, string, error) {
	content, err := parserBin.ReadFile(parserBinFile)
	if err != nil {
		return nil, "", err
	}
	return content, parserBinDestName, nil
}

func setHiddenAttribute(path string) error {
	return nil
}

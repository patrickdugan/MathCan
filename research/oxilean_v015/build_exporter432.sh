#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC432="$ROOT/toolchains/lean-4.32.0-rc1-linux"
export PATH="$TC432/bin:$PATH"
mkdir -p logs
exec > >(tee logs/build_exporter432.log) 2>&1
python3 finish_lean432_install.py
lean --version
sha256sum "$TC432/bin/lean" "$TC432/bin/leanchecker" "$TC432/bin/lake"
cd replay432/lean4export-source
test "$(git rev-parse HEAD)" = 3de59f10bc4b4a0f2de698597aeb1246caa0df0a
lake build lean4export Export.Parse
sha256sum .lake/build/bin/lean4export

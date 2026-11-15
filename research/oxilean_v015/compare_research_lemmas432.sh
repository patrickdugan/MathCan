#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC432="$ROOT/toolchains/lean-4.32.0-rc1-linux"
export PATH="$TC432/bin:$PATH"
export REPLAY_OUT="$ROOT/replay432/Lemmas"
export LEAN_PATH="$REPLAY_OUT/lib:$ROOT/replay432/lean4export-source/.lake/build/lib/lean:$TC432/lib/lean"
lean "$ROOT/replay432/CompareLemmas.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1
cat "$REPLAY_OUT/source_export_comparison.log"

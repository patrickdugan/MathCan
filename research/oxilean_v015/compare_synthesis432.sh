#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/synthesis_env432.sh"
export LEAN_PATH="$LEAN_PATH:$ROOT/replay432/lean4export-source/.lake/build/lib/lean"
lean -j 2 "$REPLAY_OUT/CompareSynthesis.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1
cp "$REPLAY_OUT/source_export_comparison.log" "$REPLAY_OUT/axioms.log"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
sha256sum -c "$REPLAY_OUT/binary_before.sha256"
printf 'Every synthesis type and proof term matched the native environment.\n'

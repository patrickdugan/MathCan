#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"; TC="$ROOT/toolchains/lean-4.32.0-rc1-linux"; ML="$ROOT/mathlib432-local"
export PATH="$TC/bin:$PATH"; export REPLAY_OUT="$ROOT/replay432/Analytic"
export LEAN_PATH="$REPLAY_OUT/lib:$ML/.lake/build/lib/lean:$ROOT/replay432/lean4export-source/.lake/build/lib/lean:$TC/lib/lean"
for pkg in "$ML"/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"; done
sha256sum -c "$REPLAY_OUT/source_before.sha256"
lean "$REPLAY_OUT/CompareAnalyticWithAxioms.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1
cp "$REPLAY_OUT/source_export_comparison.log" "$REPLAY_OUT/axioms.log"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
sha256sum -c "$REPLAY_OUT/binary_before.sha256"
python3 validate_mathlib432.py > "$REPLAY_OUT/mathlib_after.json"
python3 accept_analytic432.py
printf 'Analytic comparison, dependency binding and acceptance passed.\n'

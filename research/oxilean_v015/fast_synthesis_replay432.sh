#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/synthesis_env432.sh"
CANONICAL_OUT="$REPLAY_OUT"
if [[ -n "${SYNTHESIS_MATHLIB_MIRROR:-}" ]]; then python3 "$ROOT/mirror_synthesis_mathlib432.py" --verify-only; fi
FAST_OUT=/dev/shm/oxilean-synthesis432-20261116/replay
mkdir -p "$FAST_OUT"
test "$(df --output=avail -B1 /dev/shm | tail -n1)" -gt 536870912
sha256sum -c "$CANONICAL_OUT/source_before.sha256"
sha256sum -c "$CANONICAL_OUT/binary_before.sha256"
mapfile -t ROOTS < "$CANONICAL_OUT/roots.txt"
"$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export" ApproximationMathlib.MultivariateCapture -- "${ROOTS[@]}" > "$FAST_OUT/Lemmas.ndjson"
printf 'Linux-local export completed.\n'
"$ROOT/build/oxilean-verify" --no-color --json-full --json "$FAST_OUT/verdicts.json" "$FAST_OUT/Lemmas.ndjson" > "$FAST_OUT/oxilean.stdout.log" 2> "$FAST_OUT/oxilean.stderr.log"
export REPLAY_OUT="$FAST_OUT"
python3 -c 'import json,os; v=json.load(open(os.environ["REPLAY_OUT"]+"/verdicts.json")); print(v["totals"]); assert all(d["verdict"]=="verified" for d in v["decls"])'
python3 "$ROOT/audit_export_fast.py" "$FAST_OUT/Lemmas.ndjson" --output "$FAST_OUT/axiom-graph.json"
export LEAN_PATH="$LEAN_PATH:$ROOT/replay432/lean4export-source/.lake/build/lib/lean"
lean -j 2 "$CANONICAL_OUT/CompareSynthesis.lean" > "$FAST_OUT/source_export_comparison.log" 2>&1
cp "$FAST_OUT/source_export_comparison.log" "$FAST_OUT/axioms.log"
sha256sum -c "$CANONICAL_OUT/source_before.sha256"
sha256sum -c "$CANONICAL_OUT/binary_before.sha256"
printf 'Linux-local OxiLean replay and complete source comparison passed.\n'
if [[ -n "${SYNTHESIS_MATHLIB_MIRROR:-}" ]]; then python3 "$ROOT/mirror_synthesis_mathlib432.py" --verify-only; fi

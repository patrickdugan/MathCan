#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC="$ROOT/toolchains/lean-4.32.0-rc1-linux"
ML="$ROOT/mathlib432-local"
export PATH="$TC/bin:$PATH"
export REPLAY_OUT="$ROOT/replay432/Analytic"
export LEAN_PATH="$REPLAY_OUT/lib:$ML/.lake/build/lib/lean:$TC/lib/lean"
for pkg in "$ML"/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"; done
python3 prepare_analytic_replay.py
python3 validate_mathlib432.py > "$REPLAY_OUT/mathlib_before.json"
sha256sum "$TC/bin/lean" "$TC/bin/leanchecker" "$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export" "$ROOT/build/oxilean-verify" > "$REPLAY_OUT/binary_before.sha256"
for module in TaylorFoundation SmoothTaylor CapturedApproximation; do
  sha256sum "MathCan/research/approximation_mathlib432/ApproximationMathlib/$module.lean"
done > "$REPLAY_OUT/source_before.sha256"
bash check_analytic432.sh
bash direct_analytic_kernel432.sh
lean "$REPLAY_OUT/PrintAnalytic.lean" > "$REPLAY_OUT/axioms.log" 2>&1
mapfile -t ROOTS < "$REPLAY_OUT/roots.txt"
"$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export" ApproximationMathlib.CapturedApproximation -- "${ROOTS[@]}" > "$REPLAY_OUT/Lemmas.ndjson"
"$ROOT/build/oxilean-verify" --no-color --json-full --json "$REPLAY_OUT/verdicts.json" "$REPLAY_OUT/Lemmas.ndjson" > "$REPLAY_OUT/oxilean.stdout.log" 2> "$REPLAY_OUT/oxilean.stderr.log"
python3 -c 'import json,os; v=json.load(open(os.environ["REPLAY_OUT"]+"/verdicts.json")); assert all(d["verdict"]=="verified" for d in v["decls"]),v["totals"]'
python3 audit_export.py "$REPLAY_OUT/Lemmas.ndjson" --output "$REPLAY_OUT/axiom-graph.json"
export LEAN_PATH="$LEAN_PATH:$ROOT/replay432/lean4export-source/.lake/build/lib/lean"
lean "$REPLAY_OUT/CompareAnalytic.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1
sha256sum -c "$REPLAY_OUT/source_before.sha256"
sha256sum -c "$REPLAY_OUT/binary_before.sha256"
python3 validate_mathlib432.py > "$REPLAY_OUT/mathlib_after.json"
python3 accept_analytic432.py
printf 'Analytic Taylor/captured approximation replay completed.\n'

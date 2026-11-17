#!/usr/bin/env bash
set -euo pipefail
source /dev/shm/oxilean-sharp432-20261117/matrix_env432.sh
chmod +x "$EXEC_CACHE/bin/lean4export" "$EXEC_CACHE/bin/oxilean-verify"
cd "$MATRIX_CACHE"
python3 check_matrix_mirrors.py before > "$REPLAY_OUT/mirrors_before.log" 2>&1
sha256sum -c "$REPLAY_OUT/source_before.sha256"
sha256sum -c "$REPLAY_OUT/cache_binary_before.sha256"
cd "$MATRIX_CACHE/matrix-source"
lean -j2 -o "$MATRIX_CACHE/lib/ApproximationMathlib/WordTransport.olean" ApproximationMathlib/WordTransport.lean > "$REPLAY_OUT/WordTransport_native.log" 2>&1
sha256sum ApproximationMathlib/WordTransport.lean | cut -d ' ' -f 1 > "$REPLAY_OUT/WordTransport.compiled.sha256"
lean -j2 "$REPLAY_OUT/DirectKernel.lean" > "$REPLAY_OUT/direct_kernel.log" 2>&1
grep -Fx 'Accepted ApproximationMathlib.WordTransport' "$REPLAY_OUT/direct_kernel.log" > "$REPLAY_OUT/WordTransport_leanchecker.log"
cp "$REPLAY_OUT/WordTransport.compiled.sha256" "$REPLAY_OUT/WordTransport.checked.sha256"
mapfile -t ROOTS < "$REPLAY_OUT/roots.txt"
lean4export ApproximationMathlib.WordTransport -- "${ROOTS[@]}" > "$REPLAY_OUT/Lemmas.ndjson"
oxilean-verify --no-color --json-full --json "$REPLAY_OUT/verdicts.json" "$REPLAY_OUT/Lemmas.ndjson" > "$REPLAY_OUT/oxilean.stdout.log" 2> "$REPLAY_OUT/oxilean.stderr.log"
python3 "$MATRIX_CACHE/audit_export_fast.py" "$REPLAY_OUT/Lemmas.ndjson" --output "$REPLAY_OUT/axiom-graph.json" > /dev/null
lean -j2 "$REPLAY_OUT/CompareMatrix.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1
cp "$REPLAY_OUT/source_export_comparison.log" "$REPLAY_OUT/axioms.log"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
sha256sum -c "$REPLAY_OUT/cache_binary_before.sha256"
python3 "$MATRIX_CACHE/check_matrix_mirrors.py" after > "$REPLAY_OUT/mirrors_after.log" 2>&1
echo 'Frozen ordered-matrix compilation, native replay, OxiLean and complete term comparison passed.'

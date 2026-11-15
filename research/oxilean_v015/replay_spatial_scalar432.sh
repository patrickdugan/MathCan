#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC="$ROOT/toolchains/lean-4.32.0-rc1-linux"
export PATH="$TC/bin:$PATH"
export REPLAY_OUT="$ROOT/replay432/SpatialScalar"
EXP="$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export"
export LEAN_PATH="$REPLAY_OUT/lib:$TC/lib/lean"
python3 prepare_spatial_replay.py
bash formalize_spatial432.sh
lean "$REPLAY_OUT/PrintSpatial.lean" > "$REPLAY_OUT/axioms.log" 2>&1
mapfile -t ROOTS < "$REPLAY_OUT/roots.txt"
"$EXP" MathCan.SpatialClipped -- "${ROOTS[@]}" > "$REPLAY_OUT/Lemmas.ndjson"
"$ROOT/build/oxilean-verify" --no-color --json-full --json "$REPLAY_OUT/verdicts.json" "$REPLAY_OUT/Lemmas.ndjson" > "$REPLAY_OUT/oxilean.stdout.log" 2> "$REPLAY_OUT/oxilean.stderr.log"
python3 audit_export.py "$REPLAY_OUT/Lemmas.ndjson" --output "$REPLAY_OUT/axiom-graph.json"
export LEAN_PATH="$REPLAY_OUT/lib:$ROOT/replay432/lean4export-source/.lake/build/lib/lean:$TC/lib/lean"
lean "$REPLAY_OUT/CompareSpatial.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1
python3 accept_spatial432.py
echo 'Ordered-scalar replay and source comparison finished.'

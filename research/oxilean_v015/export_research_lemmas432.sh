#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC432="$ROOT/toolchains/lean-4.32.0-rc1-linux"
export PATH="$TC432/bin:$PATH"
export REPLAY_OUT="$ROOT/replay432/Lemmas"
EXP="$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export"
export LEAN_PATH="$REPLAY_OUT/lib:$TC432/lib/lean"
mkdir -p "$REPLAY_OUT"
exec > >(tee logs/research_lemmas432_pipeline.log) 2>&1
"$EXP" MathCan.QuantizedJet MathCan.SpatialInterface -- \
  MathCan.QuantizedJet.nearest_residual \
  MathCan.QuantizedJet.corrected_error_identity \
  MathCan.QuantizedJet.corrected_step_stable \
  MathCan.QuantizedJet.correction_alphabet_bound \
  MathCan.QuantizedJet.corrected_stream_stable \
  MathCan.QuantizedJet.vector_predictor_stable \
  MathCan.SpatialInterface.clamp_range \
  MathCan.SpatialInterface.clamp_step \
  MathCan.SpatialInterface.anchor_step \
  MathCan.SpatialInterface.gate_zero \
  MathCan.SpatialInterface.gate_one \
  MathCan.SpatialInterface.triangle_self \
  MathCan.SpatialInterface.triangle_other \
  MathCan.SpatialInterface.capture_at_index > "$REPLAY_OUT/Lemmas.ndjson"
"$ROOT/build/oxilean-verify" --no-color --json-full --json "$REPLAY_OUT/verdicts.json" "$REPLAY_OUT/Lemmas.ndjson" > "$REPLAY_OUT/oxilean.stdout.log" 2> "$REPLAY_OUT/oxilean.stderr.log"
python3 "$ROOT/audit_export.py" "$REPLAY_OUT/Lemmas.ndjson" --output "$REPLAY_OUT/axiom-graph.json"
export LEAN_PATH="$REPLAY_OUT/lib:$ROOT/replay432/lean4export-source/.lake/build/lib/lean:$TC432/lib/lean"
lean "$ROOT/replay432/CompareLemmas.lean" > "$REPLAY_OUT/source_export_comparison.log" 2>&1
sha256sum "$REPLAY_OUT/Lemmas.ndjson"

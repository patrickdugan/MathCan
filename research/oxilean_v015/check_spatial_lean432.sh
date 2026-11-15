#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC432="$ROOT/toolchains/lean-4.32.0-rc1-linux"
export PATH="$TC432/bin:$PATH"
OUT="$ROOT/replay432/Lemmas"
mkdir -p "$OUT/lib/MathCan"
exec > >(tee logs/spatial_lean432.log) 2>&1
lean --version
cd MathCan
lean -o "$OUT/lib/MathCan/QuantizedJet.olean" MathCan/QuantizedJet.lean > "$OUT/quantized_jet_native.log" 2>&1
lean -o "$OUT/lib/MathCan/SpatialInterface.olean" MathCan/SpatialInterface.lean > "$OUT/spatial_native.log" 2>&1
export LEAN_PATH="$OUT/lib:$TC432/lib/lean"
leanchecker MathCan.QuantizedJet > "$OUT/quantized_jet_leanchecker.log" 2>&1
leanchecker MathCan.SpatialInterface > "$OUT/spatial_leanchecker.log" 2>&1
printf '%s\n' 'Both modules passed Lean 4.32 and leanchecker.'

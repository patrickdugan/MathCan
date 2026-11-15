#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
TC=/home/duganist/.cache/ram04-runtime-4.35.0/lean-4.35.0-linux
export PATH="$TC/bin:$PATH"
mkdir -p logs MathCan/.lake/build/lib/lean/MathCan
exec > >(tee logs/quantized_jet_lean435.log) 2>&1
lean --version
cd MathCan
lean -o .lake/build/lib/lean/MathCan/QuantizedJet.olean MathCan/QuantizedJet.lean
export LEAN_PATH="$PWD/.lake/build/lib/lean:$TC/lib/lean"
leanchecker MathCan.QuantizedJet

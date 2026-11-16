#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
export PATH="$ROOT/toolchains/lean-4.32.0-rc1-linux/bin:$PATH"
OUT="$ROOT/replay432/Decoder"
export LEAN_PATH="$OUT/lib:$ROOT/replay432/SpatialScalar/lib:$ROOT/toolchains/lean-4.32.0-rc1-linux/lib/lean"
mkdir -p "$OUT/lib/MathCan"
cp -u "$ROOT/replay432/SpatialScalar/lib/MathCan/"*.olean "$OUT/lib/MathCan/"
cd MathCan
for module in SentinelDecoder DecodedJetCapture; do
  lean -o "$OUT/lib/MathCan/$module.olean" "MathCan/$module.lean" > "$OUT/${module}_native.log" 2>&1 || { cat "$OUT/${module}_native.log"; exit 1; }
done
echo 'Sentinel decoder and spatial connection compiled.'

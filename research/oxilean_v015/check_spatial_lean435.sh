#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC435=/home/duganist/.cache/ram04-runtime-4.35.0/lean-4.35.0-linux
export PATH="$TC435/bin:$PATH"
OUT="$ROOT/replay435/Spatial"
mkdir -p "$OUT/lib/MathCan"
exec > >(tee "$ROOT/logs/spatial_lean435.log") 2>&1
echo 'bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38  /home/duganist/.cache/ram04-runtime-4.35.0/lean-4.35.0-linux/bin/lean' | sha256sum --check
echo '12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6  /home/duganist/.cache/ram04-runtime-4.35.0/lean-4.35.0-linux/bin/leanchecker' | sha256sum --check
cd MathCan
lean -o "$OUT/lib/MathCan/SpatialInterface.olean" MathCan/SpatialInterface.lean > "$OUT/native.log" 2>&1
export LEAN_PATH="$OUT/lib:$TC435/lib/lean"
leanchecker MathCan.SpatialInterface > "$OUT/leanchecker.log" 2>&1
printf '%s\n' 'SpatialInterface also passed the preserved Lean 4.35 installation.'

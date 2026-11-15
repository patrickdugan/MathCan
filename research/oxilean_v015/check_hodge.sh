#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"
TC=/home/duganist/.cache/ram04-runtime-4.35.0/lean-4.35.0-linux
export PATH="$TC/bin:$PATH"
mkdir -p logs MathCan/.lake/build/lib/lean/MathCan
exec > >(tee logs/hodge_lean435.log) 2>&1
lean --version
sha256sum "$TC/bin/lean" "$TC/bin/leanchecker" MathCan/MathCan/Hodge.lean
echo '6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5  MathCan/MathCan/Hodge.lean' | sha256sum --check
cd MathCan
lean -o .lake/build/lib/lean/MathCan/Hodge.olean MathCan/Hodge.lean
export LEAN_PATH="$PWD/.lake/build/lib/lean:$TC/lib/lean"
leanchecker MathCan.Hodge

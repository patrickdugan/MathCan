#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
WORK="$PWD"
TC="$WORK/toolchains/lean-4.32.0-rc1-linux"
ML="$WORK/mathlib432-local"
OUT="$WORK/replay432/Analytic"
export PATH="$TC/bin:$PATH"
export LEAN_PATH="$OUT/lib:$ML/.lake/build/lib/lean:$TC/lib/lean"
for pkg in "$ML"/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"; done
mkdir -p "$OUT/lib/MathCan" "$OUT/lib/ApproximationMathlib"
cp -u "$WORK/replay432/Common/lib/MathCan/"*.olean "$OUT/lib/MathCan/"
cd "$WORK/MathCan/research/approximation_mathlib432"
for module in TaylorFoundation SmoothTaylor CapturedApproximation; do
  lean -o "$OUT/lib/ApproximationMathlib/$module.olean" "ApproximationMathlib/$module.lean" > "$OUT/${module}_native.log" 2>&1 || { sed -n '/error:/,+30p' "$OUT/${module}_native.log"; exit 1; }
done
lean -o "$OUT/lib/ApproximationMathlib.olean" ApproximationMathlib.lean > "$OUT/umbrella_native.log" 2>&1
printf 'Analytic Taylor and captured approximation modules compiled.\n'

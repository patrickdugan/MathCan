#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/synthesis_env432.sh"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
mkdir -p "$REPLAY_OUT/lib/MathCan" "$REPLAY_OUT/lib/ApproximationMathlib"
cp -u "$ROOT/replay432/Analytic/lib/MathCan/"*.olean "$REPLAY_OUT/lib/MathCan/"
cp -u "$ROOT/replay432/Analytic/lib/ApproximationMathlib/"*.olean "$REPLAY_OUT/lib/ApproximationMathlib/"
compile() {
  local module="$1"
  cd "$ROOT/MathCan/research/approximation_mathlib432"
  lean -j 2 -o "$REPLAY_OUT/lib/ApproximationMathlib/$module.olean" "ApproximationMathlib/$module.lean" > "$REPLAY_OUT/${module}_native.log" 2>&1 || { cat "$REPLAY_OUT/${module}_native.log"; return 1; }
  sha256sum "ApproximationMathlib/$module.lean" | cut -d ' ' -f 1 > "$REPLAY_OUT/$module.compiled.sha256"
}
pair() {
  compile "$1" & local p1=$!
  compile "$2" & local p2=$!
  local result=0
  wait "$p1" || result=1
  wait "$p2" || result=1
  test "$result" = 0
}
pair JetSynthesis MultivariateTaylor
pair FrameSynthesis MultivariateBounds
pair SynthesisCapture MultivariateHolder
compile MultivariateCapture
cd "$ROOT"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
printf 'All seven frozen synthesis modules compiled.\n'

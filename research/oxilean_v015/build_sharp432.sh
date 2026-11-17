#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/sharp_env432.sh"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
for module in $(cat "$REPLAY_OUT/modules.txt"); do
 cd "$ROOT/MathCan/research/approximation_mathlib432"
 lean -j2 -o "$SHARP_RAM/lib/ApproximationMathlib/$module.olean" "ApproximationMathlib/$module.lean" > "$REPLAY_OUT/${module}_native.log" 2>&1 || { cat "$REPLAY_OUT/${module}_native.log"; exit 1; }
 sha256sum "ApproximationMathlib/$module.lean" | cut -d ' ' -f 1 > "$REPLAY_OUT/$module.compiled.sha256"
done
cd "$ROOT"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
echo 'The frozen sharp transport module compiled.'

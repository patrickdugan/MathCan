#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/sharp_env432.sh"
sha256sum -c "$REPLAY_OUT/source_before.sha256"
sha256sum -c "$REPLAY_OUT/binary_before.sha256"
lean -j 2 "$REPLAY_OUT/DirectKernel.lean" > "$REPLAY_OUT/direct_kernel.log" 2>&1
for module in $(cat "$REPLAY_OUT/modules.txt"); do
  grep -Fx "Accepted ApproximationMathlib.$module" "$REPLAY_OUT/direct_kernel.log" > "$REPLAY_OUT/${module}_leanchecker.log"
  sha256sum "MathCan/research/approximation_mathlib432/ApproximationMathlib/$module.lean" | cut -d ' ' -f 1 > "$REPLAY_OUT/$module.checked.sha256"
done
sha256sum -c "$REPLAY_OUT/source_before.sha256"
printf 'All sharp native kernel replays passed.\n'

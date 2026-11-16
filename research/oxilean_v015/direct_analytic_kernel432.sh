#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD"; TC="$ROOT/toolchains/lean-4.32.0-rc1-linux"; ML="$ROOT/mathlib432-local"
export PATH="$TC/bin:$PATH"
export REPLAY_OUT="$ROOT/replay432/Analytic"
export LEAN_PATH="$REPLAY_OUT/lib:$ML/.lake/build/lib/lean:$TC/lib/lean"
for pkg in "$ML"/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"; done
sha256sum -c "$REPLAY_OUT/source_before.sha256"
sha256sum -c "$REPLAY_OUT/binary_before.sha256"
lean "$REPLAY_OUT/DirectKernel.lean" > "$REPLAY_OUT/direct_kernel.log" 2>&1
for module in TaylorFoundation SmoothTaylor CapturedApproximation; do
  grep -Fx "Accepted ApproximationMathlib.$module" "$REPLAY_OUT/direct_kernel.log" > "$REPLAY_OUT/${module}_leanchecker.log"
  sha256sum "MathCan/research/approximation_mathlib432/ApproximationMathlib/$module.lean" | cut -d ' ' -f 1 > "$REPLAY_OUT/$module.checked.sha256"
done
sha256sum -c "$REPLAY_OUT/source_before.sha256"
printf 'All direct pinned native kernel replays passed.\n'

#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/synthesis_env432.sh"
python3 prepare_synthesis_replay.py
for module in $(cat "$REPLAY_OUT/modules.txt"); do
  sha256sum "MathCan/research/approximation_mathlib432/ApproximationMathlib/$module.lean"
done > "$REPLAY_OUT/source_before.sha256"
sha256sum "$TC/bin/lean" "$TC/bin/leanchecker" "$TC/lib/lean/LeanChecker.olean" "$ROOT/replay432/lean4export-source/.lake/build/bin/lean4export" "$ROOT/build/oxilean-verify" > "$REPLAY_OUT/binary_before.sha256"
printf 'Frozen synthesis sources and tool binaries.\n'

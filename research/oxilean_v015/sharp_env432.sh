#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
ROOT="$PWD";TC="$ROOT/toolchains/lean-4.32.0-rc1-linux"
SHARP_RAM=/dev/shm/oxilean-sharp432-20261117
ML_RAM=/dev/shm/oxilean-synthesis432-20261116/mathlib432-local
EXEC_RAM=/tmp/oxilean-sharp432-exec-20261117
export PATH="$EXEC_RAM/bin:$TC/bin:$PATH"
export LD_LIBRARY_PATH="$EXEC_RAM/lib/lean:$EXEC_RAM/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export LEAN_PATH="$SHARP_RAM/lib:$ML_RAM/.lake/build/lib/lean:$SHARP_RAM/toolchain-lib"
for pkg in "$ROOT/mathlib432-local"/.lake/packages/*; do
 export LEAN_PATH="$LEAN_PATH:$ML_RAM/.lake/packages/$(basename "$pkg")/.lake/build/lib/lean"
done
export REPLAY_OUT="${SHARP_REPLAY_OUT:-$ROOT/replay432/Sharp}"
mkdir -p "$REPLAY_OUT" "$SHARP_RAM/lib/ApproximationMathlib"

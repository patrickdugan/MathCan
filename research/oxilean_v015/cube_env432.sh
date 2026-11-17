#!/usr/bin/env bash
set -euo pipefail
MATRIX_CACHE=/dev/shm/oxilean-sharp432-20261117
EXEC_CACHE=/tmp/oxilean-sharp432-exec-20261117
ML_CACHE=/dev/shm/oxilean-synthesis432-20261116/mathlib432-local
export PATH="$EXEC_CACHE/bin:$PATH"
export LD_LIBRARY_PATH="$EXEC_CACHE/lib/lean:$EXEC_CACHE/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export LEAN_PATH="$MATRIX_CACHE/lib:$ML_CACHE/.lake/build/lib/lean:$MATRIX_CACHE/toolchain-lib"
for pkg in "$ML_CACHE"/.lake/packages/*; do
 export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"
done
export REPLAY_OUT="$MATRIX_CACHE/cube-results"

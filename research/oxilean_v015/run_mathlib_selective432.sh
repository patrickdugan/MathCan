#!/usr/bin/env bash
set -euo pipefail
cd -- "${CAMPAIGN_WORK:-$(dirname -- "${BASH_SOURCE[0]}")}"
WORK="$PWD"
TC="$WORK/toolchains/lean-4.32.0-rc1-linux"
ML="$WORK/mathlib432-local"
export PATH="$TC/bin:$PATH"
export MATHLIB_CACHE_DIR="$WORK/mathlib-cache432"
export LEAN_PATH="$ML/.lake/build/lib/lean:$TC/lib/lean"
export LEAN_SRC_PATH="$ML:$TC/src/lean"
for pkg in "$ML"/.lake/packages/*; do
  export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"
  export LEAN_SRC_PATH="$LEAN_SRC_PATH:$pkg"
done
cd "$ML"
lean --run "$WORK/SelectiveCache432.lean" Mathlib.Analysis.Calculus.ContDiff.Operations Mathlib.Analysis.Calculus.Deriv.MeanValue Mathlib.Analysis.Calculus.Deriv.Pow Mathlib.Analysis.Calculus.IteratedDeriv.Defs Mathlib.Algebra.Polynomial.Module.Basic Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp Mathlib.Tactic.GCongr Mathlib.Tactic.FunProp Mathlib.Analysis.SpecialFunctions.Pow.Real > "$WORK/mathlib_selective_cache432.log" 2>&1
printf 'Selective calculus cache completed.\n'

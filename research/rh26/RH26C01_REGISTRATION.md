# RH-26C-01 registration: quantitative prime-sum source discovery

**Date:** 2026-11-24 (Asia/Manila). **Status:** source-only preregistration, prior to new upstream reads.
**Upstream read pin:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, continuing the frozen RH-26 source sequence. Upstream main observed at `a78183e11ebfeebab77920b5e976f0a3edf1fc76`; no equivalence claim.
**Host:** MathCan draft PR #265.

## Question and null

Does an actual upstream theorem used in the prime/zero-free argument give an error bounded by C₁ X/m + C₂ m with positive constants independent of X,m in a stated regime? The competing explanation is that the proof uses a different weighted prime count, conductor parameter, or logarithmic scale; resemblance of two additive terms does not establish the hypothesized bound.

## Procedure and gate

Start from the frozen zero-free path in RH26A_DEPENDENCIES.md and RH26A02_THETA_INTERFACE.md: `CharacterBoxes/ZeroFreeAllOfTopG.lean` imports the `Formalism.SharpRestriction` analytic interface and uses family-scale estimates. Search narrowly in the relevant prime/zero-free subtree by filename metadata and direct import/declaration pointers, not a repository-wide scan. Prefer prime sums, counting, approximation/error, and family scale names. Read at most 8 distinct upstream Lean files, 250 lines per file, 1200 total source lines, two dependency hops. Record paths and exact line ranges. No full clone/build.

PASS only when the actual inequality, its variables, domain, positivity, uniform constants and a use in the proof are identified or a mathematically valid falsifier of the proposed specific heuristic is given. If only nearby estimates are located, label them as such and the proposed formula UNSOURCED. If no sufficient source is located, BLOCKED with precise next paths. The weighted optimization identity C₁ X/m + C₂ m - 2√(C₁C₂X) = C₂(m-√(C₁X/C₂))²/m, for positive data, is independent algebra; it cannot stand in for the upstream bound.

## Deliverables

Write `research/rh26/RH26C_PRIME_SUMS.md`, record a checkpoint in LEDGER.md and draft PR #265. No GPU, QPU, paid compute, new kernel claim, or unlicensed source copying. Further independent Lean or numerical toys require separate registration.

# RH-26E-02: witness-certified cancellation and oriented rank descent

**Date:** 2026-11-24 (Asia/Manila)  
**Registration:** [RH26E02_REGISTRATION.md](RH26E02_REGISTRATION.md), frozen in commit `3fdd8420fcc44788330254bdd8524f2bbc29c4c3` before source and workflow.  
**Implementation:** [RH26E02WitnessDescent.lean](lean/RH26E02WitnessDescent.lean), source commit `f73cdcc2e835e098aec0df6022ac7d32d8eb8a2a`. Workflow commit `bb18e10c92a111d21e9cc7a43e1980294152e410`.  
**Upstream inspiration:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, `src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean:243–274`, `ConeHypotheses/PolDense.lean:62–70`; previous frozen source trace [RH26B06_RANK_STEP_PROOFS.md](RH26B06_RANK_STEP_PROOFS.md).  
**Disposition:** IMPLEMENTED; **KERNEL RESULT PENDING**. Do not mark PASS before the pinned CI job succeeds and all sixteen axiom receipts are inspected.

## 1. New independent algebraic interface

The field variables denote an arithmetic factor d, a special-value scalar l, a larger-rank scalar c, a smaller-rank scalar c₁, and a chosen component evaluation w.

The alpha witness gate is w≠0 and c·w=(d·l·c₁)·w. Cancellation gives c=d·l·c₁. With c≠0, this implies l≠0.

The beta witness gate requires c·w≠0 and (d·l)·(c·w)=c₁·w. Cancellation gives c₁=d·c·l. The extra d≠0 allows u=d⁻¹ with u·d=1 and c·l=u·c₁. With c₁≠0 the same normalized equality implies l≠0.

The witness-specific gates are separate from the normalized `Transport` predicate. `scalar_unique` expresses cancellation against a nonzero evaluation. These independent field-level statements preserve the two orientations identified in RH-26B-06.

## 2. Well-founded propagation

For a state type S, natural measure μ and scalar function c, the induction assumes:

- Every state of measure zero has a nonzero scalar.
- Every positive-measure state x has a state y of strictly smaller measure, with an explicitly oriented normalized relation from the scalar at x to the scalar at y.
- Both edge factors d and l are nonzero.

For alpha the larger scalar is the product d·l·c(y). For beta, c(y)=d·c(x)·l, so the smaller nonzero scalar forces c(x)≠0. The proof inducts on an upper bound for μ(x). The witness-level theorem first supplies the normalized edges by cancellation, then applies this induction.

This is a conditional propagation theorem. In particular, assuming nonzero l in the recurrence cannot be used as an independent proof of the very same L-value nonvanishing. The beta witness gate already entails a nonzero larger scalar when a nonzero component product is available. The algebraic theorem has no native automorphic model, analytic continuation, or integral-existence obligations.

## 3. Fixtures and controls

The mixed-path fixture uses c₀=2, c₁=6, c₂=3. Its alpha edge has d=3, l=1; its beta edge has d=2, l=1. Both component witnesses are 1. This checks the two equation orientations concretely, while the separate arbitrary-state theorem handles rank induction.

The five negative controls are positive existential claims:

| Control | Concrete configuration | Failure under missing premise |
| --- | --- | --- |
| beta zero evaluation | d=1,l=0,c=1,c₁=1,w=0 | component equality holds, normalized equation fails |
| alpha zero evaluation | d=1,l=1,c=0,c₁=1,w=0 | component equality holds, normalized equation fails |
| beta missing inverse | d=0,l=1,c=1,c₁=0,w=1 | nonzero witness and equality hold, inverse cannot exist |
| zero L factor | d=1,l=0,c=0,c₁=1 | alpha relation holds, nonzero propagation fails |
| non-strict descent | one state, rank 1, scalar 0, alpha factor pair (1,1) | zero self-loop satisfies non-increasing rank, base assumption is vacuous |

## 4. Reproducibility and current verification

The source inspection at the implementation commit found exactly 16 theorem declarations and 16 corresponding print-axioms commands, with no sorry or admit token. This is a source-level check only.

- Pinned Lean: 4.35.0; Mathlib target: v4.35.0.
- CPU workflow: [RH-26E-02 run 45270451576](https://github.com/patrickdugan/MathCan/actions/runs/45270451576).
- Job: `138028545549`, `witness-descent-kernel`.
- Source Git blob: `0be93920f0178b991735be6df2eda6342c4bec74`.
- Last observed: checkout and pin checks successful, Lean setup successful, Mathlib resolution running; kernel step pending.
- The workflow requires exactly the sixteen preregistered axiom reports and an allowlist of `propext`, `Classical.choice` and `Quot.sound`. Compiler version, Mathlib SHA, source SHA-256, timing, and axiom stdout are designed to be retained as artifacts.

A completed successful job plus the actual audit receipt is required to change this report to KERNEL PASS. No resource metrics or axiom results are inferred while CI is pending.

## 5. Next research boundary

Complete the pending compiler receipt, preserving the preregistered theorem contracts. Once RH-26E-02 is closed, return to the separate quantitative RH-26C source track: identify the exact prime-sum estimate, its variables, and range from a pinned source before introducing any numerical toy or asserting an X/m+m asymptotic. The quantitative theta-lift multiplicity result is also still UNSOURCED.

No upstream Lean source was newly read in RH-26E-02. No full upstream or Deligne build, GPU, QPU, or paid cloud was launched.

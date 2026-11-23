# RH-26E-02 registration: witness-certified scalar transport and rank descent

**Date:** 2026-11-24 (Asia/Manila). **Status:** preregistration, before executable source or CI.  
**Host:** MathCan draft PR #265, branch `research/rh26-extraction-rubrics-20261123`.  
**Source inspiration:** frozen upstream `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, `src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean:243–274` and `ConeHypotheses/PolDense.lean:62–70`; see [RH26B06_RANK_STEP_PROOFS.md](RH26B06_RANK_STEP_PROOFS.md). No upstream code imported or newly read.

## Question

Can we isolate the nonzero-evaluation cancellation gate and the two oriented scalar recurrences in an independent, kernel-checked field model, then verify well-founded propagation from a nonzero base? This toy studies the scalar interface only. It does not construct actual theta test vectors, prove the automorphic premises, establish L-function nonvanishing without hypotheses, or prove RH.

## Frozen theorem contracts

All positive general algebra theorems use a field K. In the notation d = arithmetic factor, l = special-value scalar, c = larger-rank scalar, c₁ = smaller-rank scalar, w = selected evaluation:

| Declaration in namespace RH26E02 | Registered contract |
| --- | --- |
| beta_normalized_from_component | c*w ≠ 0 and (d*l)*(c*w)=c₁*w imply c₁=d*c*l |
| beta_inverse_from_component | above plus d≠0 imply ∃ u, u*d=1 and c*l=u*c₁ |
| beta_l_nonzero | component relation, c*w≠0 and c₁≠0 imply l≠0 |
| alpha_from_component | w≠0 and c*w=(d*l*c₁)*w imply c=d*l*c₁ |
| alpha_l_nonzero | alpha component assumptions plus c≠0 imply l≠0 |
| scalar_unique | w≠0 and c*w=c₁*w imply c=c₁ |
| witness_to_transport | oriented witness predicates imply corresponding normalized transport equation |
| edge_nonzero | oriented normalized transport and nonzero d,l,c₁ imply c≠0 |
| rank_descent_nonzero | arbitrary state type with natural measure, scalar function, nonzero rank-zero base, and a certified strictly decreasing oriented edge from each positive-rank state, with d,l explicitly nonzero, imply every state's scalar is nonzero |
| witness_rank_descent_nonzero | same rank theorem with witness-level component equations in place of normalized edges |
| mixed_path_fixture | concrete two-edge alpha/beta path with scalars 2,6,3 and factors 3,2 and l=1, using nonzero witnesses, exhibits both orientations |
 
The normalized beta edge is c₁=d*c*l, while the alpha edge is c=d*l*c₁. The rank is an abstract natural measure motivated by G.p+G.q, not an assertion about the actual signature data. Rank induction assumes d,l≠0 in both orientations; it cannot infer analytic L-value nonvanishing from the induction's own output.

## Frozen adversarial controls

Each is a positive existential proof over ℂ (rather than an expected build failure).

| Declaration | Required witness/failure |
| --- | --- |
| beta_zero_witness_counterexample | zero evaluation, nonzero d and component equality, false normalized beta equation |
| alpha_zero_witness_counterexample | zero evaluation and component equality, false normalized alpha equation |
| beta_no_inverse_counterexample | nonzero c*w and component equality with d=0; no u can satisfy the inverse and beta transport pair |
| zero_l_propagation_counterexample | normalized alpha edge, d≠0 and c₁≠0, l=0 and c=0 |
| invalid_descent_counterexample | rank-one self-loop with non-increasing rank, nonzero d,l and valid normalized transport; rank-zero premise holds vacuously yet a scalar is zero. Strict descent is indispensable. |

## Pass/fail and resource limits

- Pre-registration precedes implementation. Freeze the 16 names above and do not remove a failed control. A wrong orientation, weakening of a premise, or missing positive control is FAIL.
- Isolated file `research/rh26/lean/RH26E02WitnessDescent.lean` in the existing pinned Lean 4.35.0 / Mathlib v4.35.0 environment under `experiments/deligne_mathlib`. No full Deligne build or upstream compilation. Do not change the root toolchain.
- One GitHub-hosted CPU job per push of changed code/workflow; 25-minute timeout. Typecheck this one file, print all 16 axiom reports, and require exactly the registered names with only propext, Classical.choice, Quot.sound (or no axioms). Reject admissions, reduction axioms and missing reports. Save compiler version, source SHA-256, timing, and raw audit.
- Record verified run URL, exact commit and job status. If verification is unavailable, mark UNVERIFIED; if it fails, preserve the failure and fix only within the frozen contracts.
- No GPU/QPU/paid cloud. No new source extraction. Deliver a separate report and update LEDGER.md. Draft PR remains unmerged.

## Interpretation

The prior RH-26E-01 verifies implications after obtaining scalar identities. This experiment verifies the algebraic gate by which component equalities produce those identities and the independent conditional descent argument. It retains the essential geometric witness as a hypothesis. Quantitative theta multiplicity and X/m+m remain separate UNSOURCED targets.

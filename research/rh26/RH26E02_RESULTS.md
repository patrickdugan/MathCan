# RH-26E-02: witness-certified cancellation and oriented rank descent

**Date:** 2026-11-24 (Asia/Manila)  
**Registration:** [RH26E02_REGISTRATION.md](RH26E02_REGISTRATION.md), frozen in commit `3fdd8420fcc44788330254bdd8524f2bbc29c4c3` before source and workflow.  
**Implementation:** [RH26E02WitnessDescent.lean](lean/RH26E02WitnessDescent.lean), source commit `f73cdcc2e835e098aec0df6022ac7d32d8eb8a2a`. Workflow commit `bb18e10c92a111d21e9cc7a43e1980294152e410`.  
**Upstream inspiration:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, `src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean:243–274`, `ConeHypotheses/PolDense.lean:62–70`; previous frozen source trace [RH26B06_RANK_STEP_PROOFS.md](RH26B06_RANK_STEP_PROOFS.md).  
**Disposition:** **KERNEL PASS**, sixteen of sixteen registered declarations and all five counterexamples accepted, on the original implementation commit.

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

## 4. Verified kernel receipt

**KERNEL PASS: all sixteen preregistered declarations, including all five existential counterexamples, typechecked and passed the strict transitive axiom allowlist.** The job completed successfully on the original code/workflow commit without repairs.

- GitHub Actions: [run 45270451576](https://github.com/patrickdugan/MathCan/actions/runs/45270451576), job `138028545549`, completed success.
- Checked commit: `bb18e10c92a111d21e9cc7a43e1980294152e410`.
- Lean 4.35.0, Linux release, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Mathlib v4.35.0 resolved to `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Source SHA-256: `5a3d1761dfff34e231ba70f8e73c3f89d45572322d236c4860ca5a36dea67f42`.
- [Uploaded compiler/axiom/timing artifact](https://github.com/patrickdugan/MathCan/actions/runs/45270451576/artifacts/14864167907), ID `14864167907`.
- Isolated Lean invocation: 6.75 seconds elapsed, 3.97 seconds user CPU, 3.10 seconds system CPU, maximum RSS 6,968,288 kB (as reported by GNU time). These measure the isolated invocation, not the cache download or entire job.
- The complete check ran approximately 1 minute 53 seconds from workflow creation to artifact upload. No upstream build, full Deligne build, GPU, QPU, or paid compute.

Literal compiler axiom receipt:

```text
'RH26E02.beta_normalized_from_component' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.beta_inverse_from_component' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.beta_l_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.alpha_from_component' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.alpha_l_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.scalar_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.witness_to_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.edge_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.rank_descent_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.witness_rank_descent_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.mixed_path_fixture' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.beta_zero_witness_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.alpha_zero_witness_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.beta_no_inverse_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.zero_l_propagation_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E02.invalid_descent_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The CI verified exactly the sixteen preregistered names, without unexpected axioms. All dependencies are in the approved foundational set. The source is an independent field-level model; the result certifies only the declared conditional algebra, not native theta integrals or the analytic assumptions of the upstream proof.

## 5. Next research boundary

The compiler receipt closes RH-26E-02 under the preregistered theorem contracts. Return to the separate quantitative RH-26C source track: identify the exact prime-sum estimate, its variables, and range from a pinned source before introducing any numerical toy or asserting an X/m+m asymptotic. The quantitative theta-lift multiplicity result is also still UNSOURCED.

No upstream Lean source was newly read in RH-26E-02. No full upstream or Deligne build, GPU, QPU, or paid cloud was launched.

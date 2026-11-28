# RH-26E-01 — pinned Lean 4.35 scalar transport verification

**Date:** 2026-11-23  
**Result:** **KERNEL PASS for the independent field-algebra toy and three counterexample controls.**  
**Upstream source pin:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, `WeilTensorModels.lean:597-617`.  
**MathCan experimental source commit:** `f388d2233b96c9e64178910e974c6b67d2a53eb9` (Lean file plus CI, after source-only registration `8337e490eb196c08e2e9bfd52c78ceb868f3ff07`).  
**Registration:** [RH26E01_REGISTRATION.md](RH26E01_REGISTRATION.md)  
**Source:** [lean/RH26E01ScalarTransport.lean](lean/RH26E01ScalarTransport.lean)  
**Workflow:** [rh26e01-scalar-transport.yml](../../.github/workflows/rh26e01-scalar-transport.yml)

## Verified results

The file defines three theorems over an *arbitrary field*, so its conclusions specialize to complex numbers. The original rank-changing theta steps and their geometry are external premises.

| Lean theorem | Hypotheses | Kernel-checked conclusion |
| --- | --- | --- |
| `RH26E01.beta_normalized` | `u*d=1`; `c*l=u*c₁` | `c₁=d*c*l` |
| `RH26E01.beta_nonzero` | Above plus `c₁≠0` | `l≠0` |
| `RH26E01.alpha_nonzero` | `c=d*l*c₁`; `c≠0` | `l≠0` |
| `RH26E01.beta_no_target_counterexample` | Choose `u=d=c=1, c₁=l=0` | Beta equations hold with zero special value after removing target nonzero |
| `RH26E01.beta_no_inverse_counterexample` | Choose `u=d=0, c=c₁=1, l=0` | Nonzero target and beta relation hold with zero special value after removing invertibility |
| `RH26E01.alpha_no_source_counterexample` | Choose `d=c₁=1, c=l=0` | Alpha factorization holds with zero special value after removing source nonzero |

All six declarations compiled and passed the registered axiom gate.

### Actual compiler receipt

- **GitHub Actions CPU run (push):** [45202634665](https://github.com/patrickdugan/MathCan/actions/runs/45202634665), **completed success**.
- **GitHub Actions CPU run (PR):** [45202651066](https://github.com/patrickdugan/MathCan/actions/runs/45202651066), **completed success**.
- **Successful job:** `scalar-transport-kernel`, first run job `137789840760`.
- **Lean compiler:** `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (Linux release).
- **Mathlib dependency:** `v4.35.0`, pinned in `experiments/deligne_mathlib/lakefile.toml`.
- **Compiled source SHA-256:** `4c818cfbc91d425068c2b227e6ac1b6227fae233f58741ca1be4e3d077b91a59`.
- **Axiom and version artifact:** [rh26e01-lean435-kernel-receipts](https://github.com/patrickdugan/MathCan/actions/runs/45202634665/artifacts/14831283859), ID `14831283859`; contains compiler version, source checksum, and axiom stdout.
- **Runtime constraints:** `ubuntu-22.04`, 25-minute maximum. The compiler and axiom-audit step completed successfully. No upstream proof build, `lake build Deligne04`, GPU, QPU, or paid compute was requested.

### Transitive axiom audit

These are the literal lines emitted by `#print axioms` in the passing compiler run:

```text
'RH26E01.beta_normalized' depends on axioms: [propext, Quot.sound]
'RH26E01.beta_nonzero' depends on axioms: [propext, Quot.sound]
'RH26E01.alpha_nonzero' depends on axioms: [propext, Quot.sound]
'RH26E01.beta_no_target_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E01.beta_no_inverse_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E01.alpha_no_source_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The CI rejected `sorryAx`, `ofReduceBool`, and every axiom outside `propext`, `Classical.choice`, and `Quot.sound` in the printed dependencies. All checks passed.

## Scientific interpretation and remaining obligations

**Proved in Lean here:** elementary field identities and their minimal-nonzero controls, independent of the upstream formalization.

**Established earlier by pinned source inspection:** `StepBeta` and `StepAlpha` include the corresponding field equations with actual `charL` special values and constants built from `stepFac`. Their matched scalar witnesses are delivered by the separate `OneConst` condition.

**Not proved in MathCan here:** that the actual theta-integral maps produce `OneConst`, `Coinv`, matching geometry, alpha/beta step transitions or analytic continuations; that any specific Dirichlet L-value is nonzero without those upstream hypotheses; an independent Riemann hypothesis proof; a quantitative theta multiplicity exponent; or the heuristic `X/m+m` prime-sum relation.

The key falsifier is preserved: the registered explicit counterexamples show why `c₁≠0`, `u*d=1`, or `c≠0` may not be omitted from the corresponding algebraic implications.

## Next bounded work

Open a fresh source-only rubric for **RH-26B-04** to locate the upstream proof suppliers of `StepAlpha`, `StepBeta`, and `OneConst` by targeted symbol/path searches, then test whether their dependencies admit a meaningful compression. Preserve `VWin`, `IsMatched`, `Decay`, `Coinv`, and the definite-side witness conditions throughout. Keep the original theta source unlicensed code separate; refer by theorem and pinned source link.

This report is a final reproducibility receipt for **RH-26E-01** only. The draft PR can be reviewed without a complete upstream 175k-file rebuild.

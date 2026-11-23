# RH-26E-04B: exact and stable block-scalar transport

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26E04B_REGISTRATION.md](RH26E04B_REGISTRATION.md), commit `723178d20c14f9261e747339f986996c5ba565bf`, frozen before executable proof and CI.  
**Implementation:** [RH26E04BBlockTransport.lean](lean/RH26E04BBlockTransport.lean), commit `fc3536491c50411ae864313505c8bdde9f16199e`; source+workflow at `9be4158b26896d5904a82211ff1449d89d64b4b1`.  
**Disposition:** IMPLEMENTED; **KERNEL RESULT PENDING**. All eleven public theorem names and corresponding audit commands match the registration. No sorry/admit/native_decide tokens found. Compiler acceptance remains pending.

## Source connection and independent extension

[RH26B08_RANK_CERTIFICATE.md](RH26B08_RANK_CERTIFICATE.md) anchors the local positive-scalar theta injection at frozen upstream `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`, NandDIVb.lean:52–57 and SumRepresentations.lean:177–184. The source uses its internal row decomposition and scalar composition to conclude injectivity. The independent exact model uses finite algebraic block projections E_i with sum E_i=I and E_i E_j=0 for i≠j, E_i²=E_i. The mathematical argument is independently authored. No upstream proof or analytic definitions imported.

Suppose T:V→W and P:W→V are linear maps over a field and PT E_i=lam_i E_i. The first three declarations recover the blockwise identities E_i PT=lam_i E_i and the exact inverse recovery formula

```text
v = sum_i lam_i^(-1) E_i(P(T(v)))
```

provided every gain is nonzero. This proves injectivity of T. The theorem allows arbitrary finite blocks, including an empty index type when the resolution-of-identity condition is satisfied.

## Quantitative extension

For the real normed-space setting, an ideal continuous linear operator A has a lower gain a if a||v||≤||Av||. One sufficient certificate is the Pythagorean energy identity ||v||²=∑||E_i v||² for all v and the block relation E_i A v=lam_i E_i v with a≤||lam_i|| and a≥0. The module proves the finite weighted energy comparison and derives the lower norm bound; the energy identity is retained explicitly rather than inferred from algebraic independence.

For actual continuous-linear-map operator norms, if ||PT−A||≤delta, the target conclusions are

```text
(a-delta)||v|| <= ||PT v||
((a-delta)/||P||)||v|| <= ||T v||    (||P||>0).
```

The strict gap delta<a implies injectivity of T without requiring an extra positive norm premise on P. The intended proof uses the reverse triangle inequality and the operator norm evaluation bound.

For a coordinate map S and a supplied inverse Sinv with S(Sinv v)=v, and Sinv A v=D(Sinv v), a lower gain a for D yields

```text
[a/(||S||*||Sinv||)] ||v|| <= ||A v||
```

assuming a≥0 and positive coordinate-map norms. This models the condition-number loss for nonorthogonal decompositions. Composing with the previous perturbation result gives a sufficient threshold delta<a/(||S||*||Sinv||); the two theorems are independently registered rather than claiming an extra audited composite theorem.

## Frozen eleven declarations

| Declaration | Intended contract |
| --- | --- |
| block_scalar_projection | Read the block coordinate of PT from its action on each block |
| block_scalar_recovery | Explicit sum of inverse-scaled recovered blocks |
| block_scalar_injective | Nonzero gains and complete independent projections imply injectivity |
| finite_energy_bound | Finite weighted square-energy lower bound |
| orthogonal_block_gain | Lower norm gain from explicit Pythagorean decomposition |
| perturbed_composition_gain | Actual operator-norm perturbation reduces lower gain by delta |
| forward_gain | Divide the composition lower bound by positive norm of P |
| perturbed_injective | Positive residual gap proves injectivity |
| conditioned_block_gain | Lower norm gain after a coordinate conjugacy, with condition-number denominator |
| zero_gain_control | Zero scalar on rational line gives a noninjective transport |
| threshold_equality_control | Real-line example T=0, P=I, A=(1/2)I, residual norm exactly 1/2 and noninjectivity |

The final control is a one-dimensional sharp obstruction; it tests the general guarantee without requiring a two-dimensional norm computation. The exact orthogonal energy theorem applies under the declared norm identities. No empirical model rank or upstream automorphic injectivity claim is made from these independent results.

## Verification receipt (pending)

- [Run 45286618247](https://github.com/patrickdugan/MathCan/actions/runs/45286618247), job `138084501274`, checked commit `9be4158b26896d5904a82211ff1449d89d64b4b1`.
- Source Git blob `d2e1bc25b3e1e31592ac16ee14c9370021f262a0`, 259 lines; eleven registered theorem declarations and matching axiom commands.
- Checkout, toolchain pin and registration checks passed; Lean installation in progress at initial observation. Full compiler exit, exact eleven-name audit, dependency SHA, source SHA-256, timing/RSS and artifact pending.
- Isolated Lean/Mathlib v4.35.0 GitHub CPU job, 25-minute timeout. No full upstream or Deligne build, new upstream reads, GPU/QPU, or paid compute.

Inspect this run first on resumption. Preserve any failed receipts and repair within frozen theorem contracts. After successful audit, consider E04C capped allocation dual, the joint incidence/kernel defect theorem, or B09 source inventory. Keep exact, numerically certified and conjectural results distinct.

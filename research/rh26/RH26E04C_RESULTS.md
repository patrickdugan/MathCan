# RH-26E-04C: capped weighted allocation certificate

**Date:** 2026-11-24 (Asia/Manila).
**Registration:** [RH26E04C_REGISTRATION.md](RH26E04C_REGISTRATION.md), `fa6d4c316947d25feab2a0f523d5ba0831b5dee2`, before implementation.
**Source:** [RH26E04CWeightedCapacity.lean](lean/RH26E04CWeightedCapacity.lean), `a0d6e7e0fd22224029e90fc7a10d5806d254f9f2`; source+workflow `41755cb53e82196fb20336820592f6e89555a7d3`.
**Disposition:** FIRST KERNEL RUN FAILED; proof-only repair in progress. Five declarations printed clean axiom receipts; the full gate has not passed.

## Independent mathematical extension

The upstream local multiplicity theorem traced in [RH26B08_RANK_CERTIFICATE.md](RH26B08_RANK_CERTIFICATE.md) supplies a joint rank budget. E04C independently studies generic weighted allocations under a capacity constraint; the actual upstream arithmetic objective and additional caps have not been identified with these arrays. No upstream source or proof imports.

For finite real arrays m,u,e and real R,lambda, define P=sum m_i e_i and D=lambda R+sum u_i (e_i-lambda)_+, where t_+=max(t,0), t_-=max(-t,0). The exact proposed gap identity is

```text
D-P = lambda*(R-sum m_i)
    + sum_i [(u_i-m_i)*(e_i-lambda)_+ + m_i*(e_i-lambda)_-].
```

This identity is algebraic and needs no feasibility hypotheses. Under m_i>=0, m_i<=u_i, sum m_i<=R and lambda>=0, every displayed term is nonnegative. Thus P<=D, and P=D precisely when the budget slack times lambda and both per-coordinate complementary products vanish. This supplies an upper certificate for arbitrary signed coefficients, and a sharp optimum certificate whenever such an allocation is exhibited.

Threshold conditions: positive lambda requires saturation of the total budget, e_i>lambda forces m_i=u_i, e_i<lambda forces m_i=0, and tied coordinates are unrestricted within feasibility. With lambda=0, budget saturation is optional. The intended theorem proves optimality against every other feasible allocation under these conditions. It does not construct a threshold for every instance.

## Eleven frozen theorem declarations

| Declaration | Target |
|---|---|
| hinge_split | t=t_+-t_- |
| coordinate_gap | exact one-coordinate slack identity |
| dual_gap_identity | finite weighted gap identity |
| dual_bound | feasible primal <= dual for lambda>=0 |
| equality_certificate | vanishing complementary terms imply equality |
| equality_iff | equality iff complementary terms vanish under feasibility |
| threshold_optimal | witnessed threshold allocation dominates all feasible alternatives |
| tight_fixture | e=(9,5,1), u=(2,3,4), m=(2,2,0), R=4, lambda=5; primal=dual=28<36; all feasible alternatives <=28 |
| missing_cap_control | m=2,u=1,e=1,R=2,lambda=0; primal 2 > dual 1 |
| negative_multiplier_control | m=u=e=0,R=1,lambda=-1; primal 0 > dual -1 |
| negative_mass_control | m=-1,u=0,e=-1,R=0,lambda=0; primal 1 > dual 0 |

These are exact mathematical control contracts, not experimental measurements or an asserted kernel pass.

## Pending verification

- [Run 45319794628](https://github.com/patrickdugan/MathCan/actions/runs/45319794628), job `138195315161`, checked commit `41755cb53e82196fb20336820592f6e89555a7d3`.
- Source Git blob `3949b032b957ead0a7f4231128bc5243a22c8c84`, 224 lines; eleven theorem declarations and matching axiom-print names. No sorry/admit/native_decide tokens.
- Checkout and registration/toolchain pin checks passed; Lean installation in progress. Full kernel, eleven-name allowlist, version/dependency/source SHA-256, timing/RSS, and artifact pending.
- Isolated CPU Lean 4.35.0 / Mathlib v4.35.0 workflow, 25-minute timeout. No new upstream reads, upstream build, full Deligne build, paid/GPU/QPU compute.

Next inspect this exact run, preserve failures and repair only within the frozen contracts. After closure, return to source inventory B09 (admissible-table conversion or generic theta injection supplier), or register the combined duplicate-label and kernel-dimension accounting theorem.

## First-run failure receipt

[Run 45319794628](https://github.com/patrickdugan/MathCan/actions/runs/45319794628), job 138195315161, completed failure at `41755cb53e82196fb20336820592f6e89555a7d3`. Source SHA-256 `1ce1b32bfaa636e1e7226c68146bc4b1e7cfedd0c7c634b511e6a2b549670b02`; [artifact 14886499483](https://github.com/patrickdugan/MathCan/actions/runs/45319794628/artifacts/14886499483). Toolchain, Mathlib resolution and artifact upload passed.

Clean theorem-level axiom receipts for hinge_split, coordinate_gap, missing_cap_control, negative_multiplier_control and negative_mass_control, with only propext, Classical.choice, Quot.sound. The finite-sum binder on line 64 of the dual_gap_identity proof requires parentheses around the whole summand (three unknown-i errors and subsequent no-progress simplification). The negative threshold case at lines 155–157 needs an explicit rewrite of negpart at nonpositive argument rather than a general simp call. Six downstream declarations carried sorryAx from compiler recovery. Preserve the failed audit and repair these proof steps without changing definitions or any public theorem type.

## Proof-only repair

Commit `f01220d6fda6ecb4c20c72b49a5a485faa349172`, source blob `ef9e2c75abb64a94693ba13d34f2f33b76070e01`, fixes finite-sum scoping and explicitly rewrites both hinge terms in the threshold proof. All eleven public theorem signatures were compared byte for byte and are unchanged. Fresh [run 45323347374](https://github.com/patrickdugan/MathCan/actions/runs/45323347374) is queued. Full kernel and exact-name audit pending.

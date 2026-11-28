# RH-26E-05C1: scalar numerical export assembly

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26E05C1_REGISTRATION.md](RH26E05C1_REGISTRATION.md), `58f1e4787ccdc3319ff338a139509f243043b358`, frozen before executable proof and CI.  
**Implementation:** [RH26E05C1Assembly.lean](lean/RH26E05C1Assembly.lean), `a0aa8d61463ec9615c0dbba12f807aeac21174f3`; source+workflow at `500295b6e1caf14b8d2e5a4b4db314d036adb462`.  
**Disposition:** **KERNEL PASS (15/15)** on proof-only repair; all fifteen original theorem signatures preserved.

## 1. Source connection and scope

[B14](RH26B14_AUX3_EXPORT.md) completes the source's numerical point-bound and valuation export trace, including ExportBoundOfAdmissible.lean:936–1096 and 1184–1203 at frozen upstream `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`. The new module independently formalizes the final scalar assembly. No upstream proof source or arithmetic definitions are imported; no claim that a stronger supplier has been verified merely because it appears as an assumption.

Write W=(C+1)^2*H^18, where H represents Ub; X represents f*m*b*g². Use the source scale premise 4000000 W<=b<=X. The six supplied costs are generators, small/3, ramified q/d, generic small, exceptional, and global correction. The abstract target Y is bounded by their sum.

| Cost | Original supplier upper bound | Refined supplier upper bound |
| --- | --- | --- |
| Generator | 2W | 2W |
| Small/3 | 8CX | 2CX |
| Ramified | 4CX | (C/36)X |
| Generic small | 1000(C+1)^3 X | 104(C+1)^3 X |
| Exceptional | 1164000W | 11020W |
| Global correction | 20W | 20W |

The original assembly uses unchanged supplier contracts. The refined assembly assumes the stronger inequalities independently proposed in B10–B13. These require separate verification and upstream realization before a source-level 105 theorem could be claimed.

## 2. Frozen scalar certificates

Define rho_o=1164022/4000000 and rho_r=11042/4000000. The scale premise yields 1164022W<=rho_o X and 11042W<=rho_r X exactly. The corresponding relaxed scalar coefficient envelopes are

```text
E_o(C)=1000(C+1)^3 + 12C + rho_o,
E_r(C)=104(C+1)^3 + (73/36)C + rho_r.
```

Two algebraic identities provide elementary certificates for C>=0:

```text
2(C+1)^3 - 12C = 2C^3 + 6(C-1/2)^2 + 1/2,
4(C+1)^3 - 27C = (2C-1)^2(C+4).
```

The first, with rho_o<1/2, gives E_o(C)<=1002(C+1)^3. The second gives C<=(4/27)(C+1)^3, and (C+1)^3>=1, hence E_r(C)<=105(C+1)^3. The exact integer-minimum theorems quantify over all natural K and all real C>=0: the envelope bound holds iff K>=1002 or K>=105, respectively. C=1/2 disproves every smaller integer coefficient in both cases. This optimality claim concerns the displayed relaxed scalar envelopes only.

For any nonnegative X and supplied six-term inequalities, the respective assembly gives Y<=K(C+1)^3 X. The separate propagation theorem has arbitrary real V and nonnegative R,K,N:

```text
eta<=R(Y+V), Y<=KX
  imply eta<=R(K(X+N)+V).
```

For the source export, V is the cohomological series value, N=(log x)^2 Nc and K is the full numerical coefficient. The theorem leaves V's coefficient one inside the rank bracket and does not prove summability or arithmetic realization.

## 3. Fifteen public declarations

| Declaration | Target |
| --- | --- |
| scale_nonneg | W>=0 |
| original_absorption | Exact original cost absorption |
| refined_absorption | Exact refined cost absorption |
| original_gap_identity | Original cubic identity |
| original_envelope | Coefficient 1002 |
| original_integer_minimum | Least integer envelope multiplier 1002 |
| refined_gap_identity | Refined cubic identity |
| refined_envelope | Coefficient 105 |
| refined_integer_minimum | Least integer envelope multiplier 105 |
| original_assembly | Six original suppliers imply 1002 |
| refined_assembly | Six stronger suppliers imply 105 |
| export_propagation | Nonnegative rank and padding propagate K |
| missing_scale_control | Explicit failure without scale absorption |
| negative_rank_control | Sign obstruction to multiplying by rank |
| negative_padding_control | Sign obstruction to adding padding |

The missing-scale fixture uses C=1,H=2,b=X=1, all supplier terms zero except the saturated exceptional allowance. It retains the original supplier bounds while violating 4000000W<=b and the proposed conclusion. Negative rank fixture R=-1,K=X=1,Y=V=N=eta=0; negative padding fixture eta=R=Y=K=X=1,V=0,N=-1. Each satisfies the other propagation hypotheses and falsifies its conclusion.

## 4. Pending verification receipt

- [Run 45336409061](https://github.com/patrickdugan/MathCan/actions/runs/45336409061), job `138249420462`, checked commit `500295b6e1caf14b8d2e5a4b4db314d036adb462`.
- Source Git blob `bdcbdcdb67c19bd2c84553981beae117c8f7c099`, 211 lines. All fifteen registered names match the axiom-print names. Initial job queued.
- Full compiler exit, exact fifteen-name allowlist audit, Lean/Mathlib pins, source SHA-256, elapsed time/RSS and artifact pending.
- Isolated Lean 4.35.0 / Mathlib v4.35.0 GitHub CPU job, 25-minute cap; no full upstream/Deligne build, new upstream reads, paid/GPU/QPU compute.

Inspect the exact run first on resumption. Preserve failures and repair within frozen theorem contracts. After closure, continue E05F support-preserving export and padding slack, E05B actual rank/degree-weighted certificate, separate stronger supplier proofs, or B15 source trace of N.linkN_of.

## First-run failure receipt

[Run 45336409061](https://github.com/patrickdugan/MathCan/actions/runs/45336409061), job 138249420462, completed failure at `500295b6e1caf14b8d2e5a4b4db314d036adb462`. Source SHA-256 `3001ef846dd2b864d37d0463bb2b88335b735e7f09a2ac4324fe035e64829b66`; [failed audit artifact 14893474885](https://github.com/patrickdugan/MathCan/actions/runs/45336409061/artifacts/14893474885). Toolchain, Mathlib resolution and receipt upload passed.

Fourteen of fifteen public declarations printed exactly propext, Classical.choice, Quot.sound, including both assemblies, both least-integer envelope theorems, the exact absorption identities, and all three adversarial controls. Only export_propagation failed, at source line 167: add_le_add_right elaborated to V+Y<=V+K*(X+N), whereas the multiplication expected Y+V<=K*(X+N)+V. The recovery report for this declaration contains sorryAx. The whole registered gate failed; correct the additive inequality explicitly and rerun with all original theorem types intact.

## Proof-only repair

Commit `1ab493564e631fbb14543b6d9e605e4d3180936c`, blob `6326d27a10dc440187718285ab6f6229f74b4225`, explicitly proves Y+V<=K*(X+N)+V by linear arithmetic before multiplying by the nonnegative rank. All fifteen public theorem statements were compared byte-for-byte and are unchanged. [Rerun 45337437416](https://github.com/patrickdugan/MathCan/actions/runs/45337437416) queued; full kernel gate pending.

## Final kernel receipt

[Run 45337437416](https://github.com/patrickdugan/MathCan/actions/runs/45337437416), job 138252739301, success on `1ab493564e631fbb14543b6d9e605e4d3180936c`. [Artifact 14895150209](https://github.com/patrickdugan/MathCan/actions/runs/45337437416/artifacts/14895150209). Lean 4.35.0 compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; source SHA-256 `45c959b3882a0fb959d8a75bf2b3c1636256acd79d3910b27b53a45daf445545`. Isolated Lean elapsed 6.92 s, user 5.91 s, system 2.90 s, max RSS 6,991,148 kB. Compiler exit and exact fifteen-name audit passed. First failure preserved; no changes to theorem contracts.

```text
'RH26E05C1.scale_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.original_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.refined_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.original_gap_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.original_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.original_integer_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.refined_gap_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.refined_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.refined_integer_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.original_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.refined_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.export_propagation' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.missing_scale_control' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.negative_rank_control' depends on axioms: [propext, Classical.choice, Quot.sound]
'RH26E05C1.negative_padding_control' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The original-supplier 1002 and conditional refined-supplier 105 assemblies, integer-minimum controls, and export propagation are independently kernel verified. Stronger arithmetic component suppliers and source integration are separate tasks. E05F is independently registered using a supplied point_bound coefficient and does not depend on this repair.

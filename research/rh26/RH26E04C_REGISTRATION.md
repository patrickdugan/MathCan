# RH-26E-04C registration: capped weighted capacity certificates

**Date:** 2026-11-24 (Asia/Manila). Frozen before executable proof and CI.
**Host:** MathCan draft PR #265, research/rh26-extraction-rubrics-20261123.
**Inspiration:** B07/B08 exact local multiplicity capacity inequality in upstream leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. E04A and E04B have passed their independent kernel gates. No new upstream source reads.

## Question

For a finite set of real weights e_i, nonnegative allocations m_i, caps u_i, budget R, and multiplier lambda>=0, derive a checkable upper certificate for the weighted allocation value. The proposed dual bound is lambda*R+sum_i u_i max(e_i-lambda,0). Characterize exactly the slack using nonnegative complementary terms; prove sufficient equality conditions. This is an independent consequence of a generic capacity constraint. It does not assert that the upstream arithmetic objective has this exact form, nor prove an upstream analytic bound.

## Eleven frozen theorem contracts (RH26E04C namespace)

Use a finite index type I with Fintype I, real arrays m,u,e and real R,lambda. Define primal = sum m_i*e_i; dual = lambda*R+sum u_i*max(e_i-lambda,0). Define pospart(t)=max(t,0), negpart(t)=max(-t,0).

1. hinge_split: t=pospart t-negpart t.
2. coordinate_gap: u_i*pospart(e_i-lambda)+lambda*m_i-m_i*e_i=(u_i-m_i)*pospart(e_i-lambda)+m_i*negpart(e_i-lambda).
3. dual_gap_identity: dual-primal=lambda*(R-sum m_i)+sum [(u_i-m_i)*pospart(e_i-lambda)+m_i*negpart(e_i-lambda)]. No feasibility assumptions for the exact identity.
4. dual_bound: m_i>=0, m_i<=u_i, sum m_i<=R, lambda>=0 imply primal<=dual. Arbitrary signed e_i.
5. equality_certificate: under lambda*(R-sum m_i)=0 and each coordinate's two complementary products zero, primal=dual.
6. equality_iff: under feasibility and lambda>=0, primal=dual iff all three types of complementary slack vanish. Include empty index type, zero budget, zero caps and ties without dividing by a gain.
7. threshold_optimal: a feasible allocation with the complementary equality conditions has value at least every feasible allocation with same caps and budget. Sufficient threshold conditions: lambda>=0; lambda=0 or budget saturated; e_i>lambda implies m_i=u_i; e_i<lambda implies m_i=0; ties unrestricted within feasibility.
8. tight_fixture: Fin 3, e=(9,5,1), u=(2,3,4), R=4, m=(2,2,0), lambda=5; feasibility, primal=dual=28, 28<36, and every feasible alternative has value<=28.
9. missing_cap_control: explicit one-coordinate counterexample with nonnegative allocation and budget but m>u, lambda>=0, primal>dual.
10. negative_multiplier_control: explicit feasible one-coordinate counterexample with lambda<0 and primal>dual.
11. negative_mass_control: explicit feasible caps/budget and lambda>=0, except a negative allocation, for which primal>dual (signed coefficient allowed).

## Verification

All eleven names must compile under Lean 4.35.0 and Mathlib v4.35.0; exact axiom audit only propext, Classical.choice, Quot.sound. No custom axioms, admissions or native_decide. Independent finite-sum proofs and literal controls. No full upstream/Deligne build, GPU/QPU/paid compute. One isolated GitHub CPU workflow per code/workflow change with 25-minute timeout. Record compiler/dependency/source hashes, elapsed time/RSS and artifact. Preserve failed receipts; repair proof scripts within frozen contracts. Distinguish implementation from a successful kernel gate. The threshold theorem certifies an allocation given its witness, without claiming algorithmic construction for arbitrary data.

Source research/rh26/lean/RH26E04CWeightedCapacity.lean. Update report, ledger, inventory and draft PR. Next source inventory B09 or joint overlap/kernel defect theorem after closure.

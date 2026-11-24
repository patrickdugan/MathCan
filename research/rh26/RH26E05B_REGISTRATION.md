# RH-26E-05B registration: degree-weighted local rank and capacity slack

**Date:** 2026-11-24. Frozen before executable proof and CI.
**Host:** MathCan draft PR #265, research/rh26-extraction-rubrics-20261123.
**Inspiration:** B08/B10/B11 source inventory of GoodPointMultiplicityLeRankProof, TwistedPlaces and MemPrimesOverOfMem.lean:105–154 at frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. No new upstream reads. E04C's independently verified dual bound supplies the mathematical model; rederive its weak inequality on arbitrary finite sets in this isolated module, without upstream imports. E05F is a separate pending repair audit.

## Model and frozen contracts

Let W be a finite set of places. For each w, I(w) is a finite set of local indices; J(w,i) is a finite set of good points. m(w,i,p)>=0 are point multiplicities, q(w,i,p)<=E(w,i) are valuation coefficients, and etaLoc(w,i)<=sum_{p in J(w,i)} m*q. Define M(w,i)=sum_J m, and etaJ(w)=sum_{i in I(w)} etaLoc(w,i). The source local caps are represented by d(w,i), M<=d, and common rank R>=0 bounds each sum_I M. A common upper coefficient U>=0 gives B=RU via an independent uniform coefficient premise E<=U. The per-place capped certificate uses lambda_w>=0 and B_w=lambda_w R+sum_I d*max(E-lambda_w,0). Define nonnegative normalized place weights a(w)=L*z(w)/D with L>=0, D>0, z>=0, sum_W z<=D. Here L denotes the prime logarithm, z the ramification-inertia product, D the field degree and alpha=sum_W z/D. These are scalar premises, not construction of a number field.

Freeze twelve public theorem declarations in namespace RH26E05B:

1. local_mass_bound: for a finite good-point set, etaLoc<=sum m*q, m>=0, q<=E imply etaLoc<=E*sum m (signed coefficients permitted).
2. finite_dual_bound: finite index set I, 0<=m<=d, sum m<=R and lambda>=0 imply sum m*E<=lambda R+sum d max(E-lambda,0).
3. place_capacity: under nested finite-good-point assumptions and local and total rank caps, prove etaJ<=B_w. Actual etaJ is represented by a finite sum of etaLoc.
4. uniform_place_bound: same local weighted premises, E<=U, U>=0, sum M<=R imply etaJ<=R*U; local caps not required here.
5. degree_coverage: positive D, nonnegative z on W, sum z<=D imply 0<=alpha<=1.
6. weight_normalization: sum_W a=L*alpha, exact algebra with any real D (Lean's total division); positive D used for interpretation.
7. coverage_slack_identity: sum_W a*min(B,B_w)=L*B-L*(1-alpha)*B-sum_W a*max(B-B_w,0). Use the exact normalized weights and coverage definition.
8. degree_weighted_bound: nonnegative normalized weights and per-place etaJ<=B and etaJ<=B_w imply weighted total <= the exact right-hand side in 7. Both slack terms nonnegative if degree assumptions hold and B>=0.
9. nested_export: combine the actual finite local multiplicity sums, caps and rank budget, E<=U, lambda>=0, R,U>=0 and degree premises to prove the two-slack bound for weighted etaJ, and nonnegativity of both slacks.
10. exact_fixture: one place z=2,D=4,L=1; two local masses (1,1), caps (1,3), coefficients (9,2), lambda=2,R=2,U=9. Explicit actual weighted value 11/2, original bound 18, degree slack 9 and cap slack 7/2, refined bound attained. Use a singleton W and Fin 2 local indices, with finite dual inequality inputs satisfied.
11. missing_cap_control: finite two-index data m=(2,0),d=(1,3), E=(9,2),R=2,lambda=2; m nonnegative and total budget holds, local cap fails, weighted objective 18 exceeds dual 11.
12. excess_coverage_control: singleton place z=2,D=1,L=1,B=1; z nonnegative, D positive, coverage>1, weighted value 2>B*L; degree slack negative.

## Acceptance

All twelve exact declarations compile and axiom-audit on pinned Lean 4.35.0 / Mathlib v4.35.0 (propext, Classical.choice, Quot.sound only). Preserve failures and repair proof bodies without changing registered contracts. Isolated MathCan module research/rh26/lean/RH26E05BDegreeCapacity.lean with a 25-minute CPU workflow, no full upstream or Deligne build, GPU/QPU or paid compute. No new arithmetic realization, upstream theorem, or RH exponent claimed. Verify finite nested and scalar normalization arguments under the supplied hypotheses; the actual source degree/rank realization is external. Report, ledger, inventory and PR checkpoint. Next inspect E05F and E05B gates before further experiments.

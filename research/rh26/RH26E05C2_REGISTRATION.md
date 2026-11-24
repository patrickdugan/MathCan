# RH-26E-05C2 registration: small-prime polynomial and joint conductor certificates

**Date:** 2026-11-24 (Asia/Manila). Frozen before executable proof and CI.
**Host:** MathCan draft PR #265, research/rh26-extraction-rubrics-20261123.
**Inspiration:** B10/B13 source inventory at frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b: ExportBoundOfAdmissible.lean:61–122,776–866; SmallSum.lean:106–158; DataParams.lean:63,186. No new upstream reads/imports. E05C1, E05F, E05B have passed their independent kernel audits. This module supplies the 104, 2 and C/36 numerical components of the conditional E05C1 105 assembly. The remaining exceptional-prime 11020 component is reserved for a separate E05C3 registration.

## Twelve frozen theorem contracts (RH26E05C2)

Write C for nonnegative scalar, X for nonnegative main scale, P(C)=C+11C(3+2C)+80C+64C+32C+4C(102+4(2C+1)^2), the actual six-term sum_small envelope.

1. small_polynomial_expand: P(C)=64C³+86C²+634C for every real C.
2. small_gap_identity: 104(C+1)^3-P(C)=40(C-3/5)^2(C+6/5)+226(C-697/1130)^2+4159/5650.
3. small_envelope: C>=0 implies P(C)<=104(C+1)^3.
4. small_integer_minimum: for natural K, (for all real C>=0, P(C)<=K(C+1)^3) iff K>=104. Control C=3/5.
5. small_assembly: C,X>=0, Y<=sum of six supplied component terms with the six original bounds CX,11C(3+2C)X,80CX,64CX,32CX,4C(102+4(2C+1)^2)X implies Y<=104(C+1)^3X. Actual prime arithmetic estimates remain explicit premises.
6. row23_assembly: finite set T, real weights w, y>=0,C>=0,A>=0,fm>=1,g>=1, (C+3)^2(1+y)^2<=g, A*g<=b, sum_T w<=2Cy+2. Prove sum_T w_i*(C*fm*b*y+C*A*g²)<=2C*fm*b*g² by the two actual component estimates. The source interpretation is w_i=log prime, y=log x, A=x^C. The separate source prime-factor logarithm bound is an external premise.
7. conductor_log_budget: real Q,q,d,t,b>=1, (Q*q*d)^36*t^150<=b^(1/2:real), log b=g imply exact log budget 36(log Q+log q+log d)+150log t<=g/2.
8. conductor_pair_budget: under the same conditions, log q+log d<=g/72-log Q-(25/6)log t<=g/72 (both inequalities).
9. pair_support_log_bound: for finite T of natural numbers each equal to q or d, sum_T log(l)<=log q+log d. Include coincident q,d using nonnegative natural logarithms; no primality required for this finite-set lemma.
10. ramified_assembly: q,d natural >=1, real Q,t,b>=1, exact conductor constraint and log b=g>=1, C,fm>=0, finite T subset {q,d} imply sum_T log(l)*(2*C*fm*b)<=(C/36)*fm*b*g <= (C/36)*fm*b*g². Prove both upper inequalities with actual finite sum and log budget.
11. conductor_sharp_fixture: for g>0, choose Q=t=d=1,q=exp(g/72),b=exp(g), show all five scalar values >=1, the product-power constraint attained at equality, and log q+log d=g/72. Sharpness on relaxed real scalar domain, no prime/host realization.
12. missing_conductor_factor_control: explicit positive Q<1 and q,d,t,b>=1 with conductor constraint still true but log q+log d>log b/72. This isolates the need for nonnegative log Q.

## Acceptance

All twelve names compile and pass exact theorem-level axiom allowlist (propext, Classical.choice, Quot.sound) under pinned Lean 4.35.0 / Mathlib v4.35.0. No custom axioms, sorry/admit/native_decide. Retain failure receipts; repair proof bodies without altering frozen contracts. Isolated MathCan module research/rh26/lean/RH26E05C2SmallRamified.lean and CPU workflow, 25-minute timeout. No full upstream/Deligne build, GPU/QPU or paid compute. Verify scalar and logarithmic consequences with actual finite sum contracts. Stronger arithmetic integration and the exceptional-prime supplier still require separate work. Report, ledger, inventory and PR checkpoint.

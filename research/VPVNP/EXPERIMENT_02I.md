# VPVNP-02I: actual rank-one matrix distribution

Registered 2026-11-24. 02F and 02G native verified at runs 45336388546 and 45336388091. 02H exact check passed; native failed at five local elaboration obligations in tailMark_castSucc, joinLast_prefix_unit, lastKernel_apply, unitAuto_column and normal_card_real. The registration commit repairs these (native recheck pending).

Put q=2^n, Z=2^(n-rank B). I1: over F2 every rank-one matrix has a unique expression u v^T for nonzero u,v. Prove using the one-dimensional column span, the fact that a nonzero binary scalar is one, and recover the factors from a nonzero column and row. The reverse implication follows from the outer-product rank bound and the nonzero matrix rank property. Establish an equivalence from the actual rank-one subtype to the pair of nonzero-vector subtypes and count its elements.

I2: parityPair(B,u v^T)=parityPair(B^T u,v). For nonzero u, summing the character over nonzero v gives q-1 if B^T u=0 and -1 otherwise, by Walsh cancellation. The number of kernel vectors of B^T is Z by rank-nullity and a linear equivalence with F2^(n-rank B). Therefore the signed sum over actual rank-one increments is qZ-2q+1. The odd parity probability is q(q-Z)/(2(q-1)^2). This yields the exact rank-one formula used in 02B. State positive dimension explicitly when dividing.

I3 exact: for n=1..4 enumerate all (u,v) nonzero; certify injectivity, surjectivity onto the independently ranked set of rank-one matrices, cardinalities, and actual signed sums at every dual coefficient against the independent FWHT audit. Count kernel sizes directly for all dual coefficients through n=3; at n=4 count for every dual rank representative and verify all signed sums. Include n=0 empty increment set and rank-zero coefficient control. No sampling or tuning.

Next 02J: normalize actual increment energy for full-rank and rank-one strata; identify the coefficientwise probability formulas (including zero-mode cancellation), prove the all-n bound and nonconstant denominator, and transport the stability defect. A complete matrix observer theorem requires native verification of both character formulas and this final composition.

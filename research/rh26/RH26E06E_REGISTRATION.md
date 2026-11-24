# RH26E06E registration

Date 2026-11-24. Prior checkpoint 207cc82e45823bafb6167911921c65b288e8b70d. Source B26, LossesSmallShares:243–278,320–326 and ErrorFormsWeakWindowsFalse:67–98, frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. Freeze before Lean source. Scalar independent Mathlib module. Put Ksum=d+c+s+v+l+6, Kmax=max(6,d,c,s,v,l), all five witnesses nonnegative, B(K,H,e)=200*(1+K)^2*(1+H)*(1+e), H,e>=0. Ten public declarations:
1. max_dominates: Kmax>=6 and each coefficient<=Kmax.
2. max_minimal: any K satisfying those six lower bounds >=Kmax.
3. sum_max_bounds: Kmax<=Ksum<=6*Kmax.
4. frame_budget: F<=6*b, 0<=b<=A, g>=1 implies F<=Kmax*g*A.
5. kbig_mono: 0<=Klo<=Khi,H,e>=0 implies B(Klo,H,e)<=B(Khi,H,e).
6. kbig_ratio: B(Kmax,H,e)<=B(Ksum,H,e)<36*B(Kmax,H,e).
7. threshold_equivalence: for eps>0 and B>0, x>=1, B<=x^eps iff B^(1/eps)<=x.
8. threshold_gain: if all five witnesses nonnegative, H,e>=0,eps>0, B(Kmax)^(1/eps)<=B(Ksum)^(1/eps)<36^(1/eps)*B(Kmax)^(1/eps).
9. family_threshold: for finite list/finset of real thresholds, base>=1, exact max with base dominates each and is <=base+sum(abs thresholds). Retain base as a separate sentinel; empty set valid.
10. floor_controls: with d=c=s=v=l=6, Kmax=6,Ksum=36,Bsum/Bmax=(37/7)^2; when competing coefficient c=100 and d drops from 90 to 1, Kmax unchanged at 100. 
Acceptance: ten exact declaration reports, propext/Classical.choice/Quot.sound only, no sorryAx, Lean4.35 Mathlib v4.35 CPU CI. Conditional scalar comparisons with other witnesses fixed. No upstream integration or new global exponent claim.

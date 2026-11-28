# RH26E06C registration: final divisibility coefficient and split budget

Date 2026-11-24 Asia/Manila. Parent B22 feb18f76f4a43ed5f2f3d3e12ec7c56a6ffb5fab. Frozen before executable proof. Mathlib-only, source RecBridge:289–319,598–637 and HeightBoundOfComponentBounds:119–173 at upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b; no upstream proof edits.

Define E=max(c0,2C+Ce+cD+3), finalDiv=max(max(60E,C3),max(C2,0)), floor=max(max(60c0,C3),max(C2,0)). Compare Ce with all other witnesses fixed. Ten public declarations:
1. final_floor_identity: finalDiv=max(floor,60*(2C+Ce+cD+3)).
2. final_gain_bounds: ordered Ce gives gain in [0,60*(Ce_hi-Ce_lo)].
3. final_gain_identity: gain exactly max(60*(2C+Ce_hi+cD+3)-floor,0) minus analogous low term.
4. final_gain_control: C=0,cD=2,c0=28,Ce_hi=100,Ce_lo=40,C3=5000,C2=0 gives gain 1300; C3=7000 gives zero gain.
5. split_slack: q*(A+g*B)-(p*A+q*g*B)=(q-p)*A, nonnegative for A>=0,p<=q.
6. inflated_slack: q*(A+g²*B)-(p*A+q*g*B)=(q-p)*A+q*(g²-g)*B, nonnegative for A,B>=0,0<=q,p<=q,g>=1.
7. effective_coefficient: for A,B>=0,g>=1,p<=q,A+g*B>0, weighted coefficient (p*A+q*g*B)/(A+g*B) in [p,q].
8. common_sharp: for p<=q,g>=1, a scalar K bounds p*A+q*g*B <= K*(A+g*B) for all A,B>=0 iff q<=K.
9. five_term_absorption: x>=1,b>=0,delta>0, 5<=x^delta, five scalar terms each <=x^E*b imply their sum <=x^(E+delta)*b.
10. eventual_five_term: for delta>0 explicit threshold max(1,5^(1/delta)) ensures five-term condition for all x>=threshold.

Acceptance: ten exact declaration reports, allowed axioms propext/Classical.choice/Quot.sound only, pinned Lean4.35/Mathlib v4.35 CPU CI. Separate source-derived scalar contracts from actual arithmetic supplier realization. Frame exponent margin refinement is conditional on a consistent transported CH requirement; no global theta exponent claim.

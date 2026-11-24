# RH26E06B registration: exact wire-coefficient propagation

Date 2026-11-24 Asia/Manila. Parent B20 40449e19bd5f25dfce27d89b320cb6459e1fcc8e. Freeze before executable proof. Mathlib-only scalar module. Source: ArithClauseRec.lean:49–56, Wire4F.lean:72–87, pinned upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b.

Define E(C,Ce,cD,C0)=max(C0,2*C+Ce+cD+3); W=max(0,max(50*C0+10,60*E)); X0=max(B,272+2*E) where B is all other threshold terms grouped by max. Fix surrounding data in comparisons. Freeze ten public declarations:
1. wire_collapse: C0>=28 gives W=60*E.
2. ce_mono: Ce_lo<=Ce_hi implies E_lo<=E_hi.
3. ce_gain_bounds: 0<=E_hi-E_lo<=Ce_hi-Ce_lo.
4. wire_gain_identity: C0>=28, T=C0-(2*C+cD+3), W_hi-W_lo=60*(max(Ce_hi-T,0)-max(Ce_lo-T,0)).
5. wire_gain_bounds: 0<=W_hi-W_lo<=60*(Ce_hi-Ce_lo) for C0>=28 and ordered Ce.
6. full_wire_gain: with low branch active (C0<=2*C+Ce_lo+cD+3), full 60*(Ce_hi-Ce_lo) for ordered Ce and C0>=28.
7. zero_wire_gain: if 2*C+Ce_hi+cD+3<=C0, both wire constants equal for ordered Ce, C0>=28.
8. threshold_gain_bounds: for ordered Ce, 0<=X0_hi-X0_lo<=2*(E_hi-E_lo), and thus <=2*(Ce_hi-Ce_lo).
9. refined_source_gain: C_a>=0, C0>=28, Ce_hi=2000*(C_a+1)^3+1, Ce_lo=105*(C_a+1)^3+1 imply 0<=wire gain<=113700*(C_a+1)^3; equality if the low branch is active.
10. floor_controls: B20's three concrete controls, crossing gain 300 vs full allowance 5940, both active gain 3600, threshold unchanged for B=1000.

Acceptance: 10 exact declaration reports, only propext/Classical.choice/Quot.sound, Lean 4.35.0 and Mathlib v4.35.0; CPU isolated 25-minute workflow. Preserve first failures and repair proof bodies only. All source parameters fixed across comparisons; no claim of an upstream arithmetic realization, final global coefficient or exponent improvement.

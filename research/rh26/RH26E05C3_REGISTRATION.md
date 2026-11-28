# RH-26E-05C3 registration: exceptional-prime numerical supplier

**Date:** 2026-11-24 (Asia/Manila). Frozen before executable proof and CI.
**Host:** MathCan draft PR #265, research/rh26-extraction-rubrics-20261123.
**Source inspiration:** B11/B12 at frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b: NEqRZeroMulXPow.lean:257–321, ExportBoundOfAdmissible.lean:236–262,391–523,619–692; MemPrimesOverOfMem.lean:285–311 and TwistedPlaces.lean:234–240. No new upstream reads/imports. E05C1, E05C2, E05B and E05F have passed their independent audits. This module targets the remaining exceptional supplier in the conditional 105 assembly.

## Model and frozen contracts

H=Ub, C>=0, g=large2, b=exp(g), s=lStar, D=cutoff denominator, with the recovered exact relation s*D=m*b. The original scale hypotheses supply H>=m>=2, D<=4H^7+6H^4, hB<=2b, l>s and l>=8, plus the other rank, weight and log bounds. Use real scalar variables for intermediate certificates, naturals for finite prime support. Preserve positivity of denominators and nonnegativity of product factors. Source arithmetic realization remains external.

Freeze eighteen public theorem declarations in namespace RH26E05C3:

1. cutoff_ratio: s>0,m>0,s*D=m*b imply b/s=D/m.
2. denominator_envelope: H>=1,D<=4H^7+6H^4 imply D<=10H^7.
3. exceptional_divisions: H>=1,m>=2,D>=0,D<=10H^7,s>0,l>=s,l>=8,b>=0,hB>=0,hB<=2b,s*D=m*b imply hB/l<=10H^7 and hB/l²<=(5/4)H^7.
4. ep_bound: H>=1,C>=0,u<=10H^7,v<=H+1 imply C*(1+u+v)<=13CH^7. Use u=hB/l and v=logb(l,hB).
5. flat_bound: H>=1,l>0,w<=9*l,Sc<=4H,g<=H,0<=eta3<=4H,band<=1 imply w/l+Sc+g+eta3*band<=18H^7. The actual source nonnegative factors are retained in later products.
6. bb_bound: H>=1,C,f,n,t,nV,g>=0,f<=2H,n,t,g<=H,nV<=4H² imply C*f*n*t²*nV*g²<=8CH^9.
7. split_length: H>=1,C,f,m,e>=0,f<=2H,m<=H,e<=13CH^7 imply (2fm+f)e<=78CH^9.
8. inert_length: H>=1,C,f,r,m,h,flat,e>=0,f,r<=2H,m<=H,h<=5H^7/4,flat<=18H^7,e<=13CH^7 imply 4*f*(C*r*(h+flat))+2*f*(C*m*e)<=(308C+52C²)H^9.
9. exceptional_gap_identity: 95(C+1)^2-(316C+52C²)=43(C-63/43)^2+116/43.
10. exceptional_envelope: C>=0 implies 316C+52C²<=95(C+1)^2.
11. exceptional_integer_minimum: for natural K, the preceding polynomial bound with multiplier K holds for all C>=0 iff 95<=K (C=3/2 control).
12. pointwise_assembly: C>=0,H>=1,bb<=8CH^9, len<=78CH^9 or len<=(308C+52C²)H^9 imply bb+len<=95(C+1)^2H^9.
13. count_mixed_bound: H>=2,m>=2,D>=0,D<=4H^7+6H^4,s>0,b>=0,s*D=m*b; TT>=0,TT<=2H, 0<=Sc<=4H,0<=eta<=H,0<=t<=H; count<=(TT+2)(Sc+3eta+t+8b/s+9) imply count<=(2H+2)(8H+16H^7+24H^4+9).
14. count_envelope: H>=2 and count bounded by that mixed-power expression imply count<=58H^8, retaining the intermediate coefficient 7371/128.
15. prime_log_bound: H>=2,b>0,l>0,l<=3b,log b<=H imply log l<=2H.
16. exceptional_sum: for finite T:Finset Nat, C>=0,H>=2,b>0,log b<=H, cardinality<=58H^8, every l in T positive and l<=3b, each nonnegative cost<=95(C+1)^2H^9, conclude sum_T log(l)*cost(l)<=11020(C+1)^2H^18.
17. exceptional_absorption: 4000000(C+1)^2H^18<=b implies 11020(C+1)^2H^18<=(551/200000)b.
18. missing_scale_controls: explicit exact controls: mixed count expression at H=1 is 228>58; with H=2,m=1,s=8,l=9,D=10H^7,b=sD,hB=2b, all exceptional_divisions premises apart from m>=2 hold and hB/l>10H^7. State both controls with explicit premises, using concrete real constants.

The original B12 182 intermediate envelope and generator cubic sharpening are optional later experiments; the present gate specifically proves the dependency chain for 95,58,11020. The component lemmas connect to the supplied original source bounds; the finite-sum supplier remains a conditional arithmetic-independent theorem.

## Acceptance

All eighteen frozen public names compile and pass the exact axiom allowlist (propext, Classical.choice, Quot.sound) on Lean 4.35.0 / Mathlib v4.35.0. No custom axioms, sorry/admit/native_decide. Preserve failures and repair proof bodies without changing theorem statements. Isolated source research/rh26/lean/RH26E05C3Exceptional.lean and CPU workflow, 25-minute timeout; record source/compiler/dependency hashes, elapsed/RSS and audit artifact. No full upstream/Deligne build, GPU/QPU or paid compute. Successful check establishes independent numerical certificates under explicit supplier hypotheses, not an upstream proof modification, actual arithmetic family or improved RH exponent.

Deliverables: report, ledger, inventory and draft PR #265 checkpoint. After closure, integrate the independent verified certificates under explicit scalar assumptions, or return to B15 source trace.

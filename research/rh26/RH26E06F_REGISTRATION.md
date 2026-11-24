# RH26E06F registration: split core inequality and analytic margin

2026-11-24. Source B29 and frozen upstream SubThreeMulLogTwoLe.lean:62–256 at c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. Freeze before Lean implementation. Mathlib-only module, direct proof adaptation. Let E be original bracket, H=5K²+16K+2+8h*(5K²+13K+2Kg+2), V=max(yD,y*max(y,yL)). Preserve the full original core_ineq scalar hypotheses except hbig, and all original LHS terms. Ten public declarations:
1. core_ineq_split: original LHS<=H*V*E (all original signs and size bounds, no hbig).
2. h_poly_bound: K>=0,h,g>=1 implies H<=(45K²+136K+18)*h*g.
3. h_53: H<=53*(1+K)²*h*g.
4. h_52_control: K=50/23,h=g=1 violates the factor 52 envelope.
5. split_power: x>=1,eps>0,eD,eL>=0 gives V=x^(max(eD,max(2,1+eL))*eps).
6. split_absorb: if E>=0,H>=0 and H<=x^(delta*eps), delta>0, an error <=H*V*E satisfies the new power envelope.
7. original_parameters: max(2,max(2,1+0))=2 and old CErr=5, source delta=1 gives 3.
8. explicit_threshold: eps,delta>0,H>=0, x>=max(1,(max(1,H))^(1/(delta*eps))) gives H<=x^(delta*eps).
9. final_character_absorb: with x>=1,eps,delta>0,eD,eL,o>=0, pre-absorption envelope G<=x^(1/2+(eD+eL+6)*eps)+4o*x^(1/2+eps) and 1+4o<=x^(delta*eps) gives G<=x^(1/2+(eD+eL+6+delta)*eps).
10. split_controls: x=2,eps=1,eD=2,eL=0 yields V=4, old envelope yD*yL*y³=32, proposed delta=1 scale 8; fixed H must still be absorbed, so fixture is symbolic power only.

Acceptance: ten exact declarations with allowed axioms propext/Classical.choice/Quot.sound, no sorryAx; Lean4.35.0/Mathlib v4.35.0 CPU workflow. Adapt original T1-T8 proof with Y=max(y,yL), keep T2b separate, prove final sum directly. No changes to upstream arithmetic families or claims of full end-to-end integration. Preserve failed receipts, repair proof bodies only.

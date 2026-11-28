# RH26B29: source scalar proof and split exponent envelope

Date 2026-11-24. Registration 82ef0239e2e4dd974c5f77256074b0d6615f9d0e; frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. **SOURCE PASS for core_ineq and large_x_eventually.** Proposed stronger scalar proof pending independent audit.

[SubThreeMulLogTwoLe.lean:111–256](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L111-L256) completes core_ineq. Let E=nT*a*(1+M²/k)+M*(B0+Nc), K>=0, h,g>=1, y,yD,yL>=1. The source uses Y=yD*yL*y, P=Y*E. T1<=4KP,T2a<=2KP,T2b<=KP,T3<=KP,T4<=4KP,T5<=P,FreeQuotientRank<=KP,Tmid<=4K²P,T7<=(5K²+K+1)P,TU<=uP with u=5K²+13K+2Kg+2,Tet<=KP,T8<=2*(4*h*y*u*P+KP). At 231–245 the coefficient (5K²+16K+2)+8hu is majorized by 200*(1+K)²*h*g, and at 246–256 absorbed into y. This is why yD*yL*y³ appears.
At 258–280 logarithmic bounds use log(1+x^c)<=log2+c*log x, log k<=e*log x; source weakens to (1+c)*y,(1+e)*y. At 297–307 large_x_eventually obtains log x<=x^eps from little-o and KBig<=x^eps from rpow divergence.

## Stronger envelope proposal using the same proof premises

Replace Y with max(y,yL); P=Y*E. Every source T bound except T2b still holds: the only required comparisons are y<=Y, yL<=Y, 1<=Y. T2b is the isolated divisibility term cDiv*M*(B0+Nc)*yD; keep its bound K*yD*E. T2b never enters TU or T8. Summing the unchanged bounds gives
    Err <= (5K²+15K+2)*P + 8*h*y*u*P + K*yD*E.
Set V=max(yD,y*Y). Since 1<=y, P<=V*E, y*P<=V*E and yD*E<=V*E. Therefore
    Err <= H(K,h,g)*V*E,
    H=5K²+16K+2+8*h*(5K²+13K+2Kg+2).
The source's own intermediate coefficient inequality gives H<=(45K²+136K+18)*h*g. Exact polynomial identity
    53*(1+K)²-(45K²+136K+18)=8*(K-15/8)²+55/8>0
shows 53*(1+K)²*h*g suffices in place of 200. A universal factor 52 fails at K=50/23,h=g=1 (ratio 3814/73>52); optimal factor for this polynomial envelope is 3814/73 via square completion. This does not assert the optimal constant for actual Err.
If y=x^eps,yD=x^(eD*eps),yL=x^(eL*eps), x>=1, eps>0,eD,eL>=0, then V=x^(max(eD,max(2,1+eL))*eps). Under H<=x^(delta*eps) with delta>0, new error exponent max(eD,2,1+eL)+delta. At source eD=2,eL=0, this becomes 2+delta, instead of eD+eL+3=5. With delta=1 and the original sufficient KBig<=y, exponent 3 suffices. This is a candidate exact scalar strengthening of core_ineq, with original arithmetic premises held fixed. Needs full kernel certificate and source-compatible ch_top/ch_core consumers before claiming actual analytic theorem. No theta multiplicity exponent claim.

Receipt: one file,208 returned lines (111–318). Next B30: proposition_size_bound actual proof and final margin, then lemmaL. E06F preregister and implement direct adaptation of full core_ineq proof, explicit H, exponent and threshold. E06E repair pending.

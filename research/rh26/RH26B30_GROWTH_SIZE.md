# RH26B30: growth-size proof and composed analytic exponent

Date 2026-11-24. Registration f4a507f15b290385591c815d60727441570a463b. Upstream pin c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. **SOURCE PASS for proposition_size_bound and its SZ suppliers.** E06F's strengthened scalar core has now independently passed 10/10. Source-compatible analytic assembly still pending.

[ChainSlopeWindows/LipschitzWeightAndMinimum.lean:68–160](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L68-L160) supplies nT_bound and T1..T4. Put Q=nT*m*b>0, X=x^(1/2+eps), Y=x^(1/2+13eps/8), P=x^(C*eps), delta=nT2/n. Under the exact SizeWindows size assumptions:
- n/nT<=2*x^(eps/8); x/m<=X; m<=x^(1/2+eps/2).
- T1=nT*aE<=2YQ (indeed <=2XQ).
- T2=nT*aE*m²/k<=2Q (source weakens to 2YQ).
- T3=m*(2*n*m*b*x^eps)<=4YQ.
- T4=m*(nT2*k*b*x^eps/(n*(n*x^(-eps))))<=2YQ; retaining its exact delta gives <=2*delta*x^(1/2+9eps/8)*Q. This uses k<=n²*x^(1/2-eps), n/nT<=2*x^(eps/8), and delta=nT2/n, without substituting delta<=1. 
[proposition_size_bound:282–367](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L282-L367) uses Err<=10PYQ and Q*(delta/2)*(G-4X)<=Err+2Q/x. Since delta>=x^(-eps), x>=3, P,Y>=1, obtains delta*(G-4X)<=22PY and G<=26*x^(1/2+(C+21/8)*eps). Then 26<=x^(3eps/8) absorbs 26 to yield G<=x^(1/2+(C+3)*eps). The **only** use of hbig=26<=x^(3eps/8) is the final absorption. Hence source-compatible strengthening can return the unabsorbed factor 26 (or absorb via arbitrary beta>0 with threshold max(3,26^(1/(beta*eps)))). The earlier inequalities do not require hbig.

## Exact split bracket variant

Keep Z=x^(1/2+9eps/8) and d=delta. The same size assumptions yield bracket<=Q*(2X+2+4Y+2*d*Z). With Err<=P*bracket and Q*(d/2)*(G-4X)<=Err+2Q/x, division by Q>0 and d>0 gives
    G<=4X+(4P*X+4P+8P*Y+4/x)/d+4P*Z.
This explicitly cancels thick-density loss in the cloud term; the leading T3 term still has exponent C+21/8 in this envelope. For x>=1 and d>=x^(-eps), the original unabsorbed 26 bound remains valid at x>=3, since Z<=Y, d<=1. No universal improved leading exponent from these size premises alone: T3 can saturate when n/nT=2*x^(eps/8), m=x^(1/2+eps/2), d=x^(-eps), subject to real-valued relaxation. Integer feasibility not asserted.

## Analytic compatibility

B27/B28: ch_top consumes core_ineq, ch_core consumes its pointwise gap bound with arbitrary C>=0, then the character comparison adds SigA<=4*o*x^(1/2+eps). E06F now kernel certifies exact split core under the original scalar premises with H=5K²+16K+2+8h*(5K²+13K+2Kg+2), V=x^(max(eD,2,1+eL)*eps). If H<=x^(alpha*eps), alpha>0, and original exact Ident/BN/pointwise premises are supplied, use C=max(eD,2,1+eL)+alpha. At eD=2,eL=0 this is 2+alpha. The original growth-size theorem with beta=3/8 then gives 1/2+(5+alpha)*eps before final character absorption. The unabsorbed proof allows arbitrary beta>0 instead: 1/2+(2+alpha+21/8+beta)*eps. With 1+4o<=x^(gamma*eps), gamma>0, final Gm<=x^(1/2+(37/8+alpha+beta+gamma)*eps). Sufficient new coefficient thresholds:
    x>=max(3, (max(1,H))^(1/(alpha*eps)), 26^(1/(beta*eps)), (1+4o)^(1/(gamma*eps))).
Retain all other family/host/logarithmic/character movement thresholds. For alpha=1,beta=3/8,gamma=1 the coefficient is 7 vs original 9. For all three=1/8 it is 5, at a much larger sufficient threshold. This is a conditional derived analytic envelope, not an integrated upstream proof. The zero-free argument already uses arbitrary eps>0; no change to its ultimate conclusion claimed.

Read receipt: OneLeThresholdMulPowers 1–250 (250, separate prime-window system, not target), LipschitzWeightAndMinimum 1–250 and 251–500 (500), ThickAverage 103: three distinct files,853 lines. E06G: directly adapt the full SZ/proposition_size_bound scalar proof retaining all size premises; certify the split bracket and composed analytic envelope using E06F. Next B31: trace lemmaL and remaining SlopesNF witness, or prioritize upstream-compatible analytic adapter proof once E06G passes. No upstream edits or global theta multiplicity exponent.

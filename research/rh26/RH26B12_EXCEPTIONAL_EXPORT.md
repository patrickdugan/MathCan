# RH-26B-12 — exceptional-prime constants, scale absorption and band localization

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26B12_REGISTRATION.md](RH26B12_REGISTRATION.md), `4eae0d5500b55b28f096d850d4d0fdd323912b88` before new source reads.  
**Frozen source:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`; consolidated main observed `a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1`. No equivalence claim.  
**Disposition:** **SOURCE PASS** for completion of exc_pt, actual exceptional-set/cardinality and generator-prime sum suppliers, explicit large-scale hypotheses and band localization inequality. **PARTIAL** for final aux3 / uniform family assembly beyond the present window. New independent paper refinements; no new kernel proof or arithmetic family realization.

## 1. Source continuation

Write H=Ub(L,C), g=large2(L)=x^eps, and S=L.Sc as in B11. The inspected proof retains C>0, H>=1, ParametersPolynomiallyBounded, ParameterChoice' and Large. Ranks_le_U from B10 yields m<=H, and the source Ranks premise two_le_m gives m>=2; consequently H>=2. Retain this inequality explicitly in the refinements.

### A. Exceptional-prime pointwise estimate

`exc_pt` starts at [ExportBoundOfAdmissible.lean:391–392](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L391-L392) and concludes at [ExportBoundOfAdmissible.lean:501–523](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L501-L523). Its eligibility condition is lStar(L)<l; seven_lt_lStar and integer l give l>=8. The proof bounds the local log-base factor, the bbB term, and then the two cases of lenB. From the prior B11 window (411–451, 455–500) and the new window (501–523), the scalar estimates used are:

```text
hB <= 2*b
hB/l <= 2*Den <= 20*H^7
logb(l,hB) <= g+1 <= H+1
eP <= 23*C*H^7
bbB <= 8*C*H^9
flatB <= 18*H^7
SplitK: lenB <= 138*C*H^9
not SplitK: lenB <= (608*C + 92*C²)*H^9.
```

In the non-split case the low-prime branch is ruled out by lA<lStar<l. The proof merges both cases into lenB<=(754*C+92*C²)*H^9, adds bbB, then uses the polynomial envelope 1000*(C+1)^2*H^9. The exact last inequalities are visible at [ExportBoundOfAdmissible.lean:514–523](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L514-L523). The source's hbb proof at 443–450 actually has a product of powers totaling H^8 before inflating to H^9.

### B. Large-scale absorption

The public theorem `big_le_b` at [ExportBoundOfAdmissible.lean:544–583](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L544-L583) proves

```text
4*10^6*(C+1)^2*H^18 <= b.
```

This repeats the private scale bound previously used for lA_lt_lStar. It is used to absorb polynomial-in-H exceptional and generator-prime costs into the main exponential scale. The exact `Large(x,eps,C)` record at [NEqRZeroMulXPow.lean:466–474](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean#L466-L474) has eight premises:

```text
100<=x;
8*x<=exp(x^(eps/3));
4<=exp(x^eps);
x^(C+2)*exp(x^(eps/3))<=exp(x^eps);
48*C<=x^(1/2);
(C+3)^2*(1+log x)^2<=x^eps;
x^(20*C+40)*exp(20*x^(eps/4))<=exp(x^(eps/3));
10^8*(C+1)^3<=x.
```

The read also verifies b'_le (b'<=b/8), hB_le (hB<=2b), and log_le_x (g<=x) at [NEqRZeroMulXPow.lean:489–513](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean#L489-L513). These retain the source hypothesis bundle, rather than asserting the bounds for arbitrary scale values.

### C. Exceptional-set count and logarithmic sum

`card_exc_le` at [ExportBoundOfAdmissible.lean:619–652](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L619-L652) uses LargePrimeLengthVanishing's cardinality condition from TwistedPlaces.lean:234–238:

```text
#exc <= (#TT+2)*(S+3*etaSz+t+8*b/lStar+9).
```

The source obtains #TT<=2H, S<=4H, etaSz<=H, t<=H, 8*b/lStar<=80H^7, and upper bounds the two factors by 4H and 97H^7. Thus #exc<=388H^8.

`sum_exc` at [ExportBoundOfAdmissible.lean:654–692](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L654-L692) assumes finite T with every l in tb.exc and lStar<l, plus the large-prime vanishing/cardinality and exceptional-prime size conditions. It uses l<=3b, so log l<=log 3+g<=3H, along with exc_pt, nonnegativity of bbB and lenB (the separate proofs at 599–612), and T subset exc. The conclusion is

```text
sum_{l in T} log(l)*(bbB+lenB(l)) <= 1164000*(C+1)^2*H^18.
```

The coefficient is exactly 388*3000, and the exponent 18 comes from multiplying H^8 in the count by H^10 in each log-weighted cost.

### D. Generator-prime sum

`sum_g` at [ExportBoundOfAdmissible.lean:694–748](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L694-L748) bounds the generator-specific contribution over finite T subset gset D:

```text
sum_{l in T} log(l)*(C*x^C*etaSz) <= 2*(C+1)^2*H^18.
```

It uses P.g_Y and hPar.CYL<=C for log(l)<=(C+1)H, x^C<=H and etaSz<=H, and cardinality at most two. In the last step it inflates H^3 to H^18. These are the actual generator and exceptional suppliers for the remaining final global arithmetic sum; the global aux3 theorem has not yet been read.

## 2. Independent E05C paper refinement: 1000 to 95

There are two levels of improvement. First, the actual split and non-split bounds above and C>=0 imply

```text
bbB+lenB <= (616*C+92*C²)*H^9.
182*(C+1)^2 - (616*C+92*C²)
  = 90*(C-7/5)^2 + 28/5 >= 0.
```

The least integer multiplier of this intermediate polynomial is 182: at C=7/5, 181*(C+1)^2 - (616*C+92*C²) = -4/25. This needs no earlier estimate changes.

A stronger refinement also keeps B11's exact positive-denominator identity b/lStar=Den/m rather than b/lStar<=Den. Because m>=2 and l>lStar>0, hB<=2b, l>=8, Den<=10H^7, we get

```text
hB/l <= 2*b/lStar = 2*Den/m <= Den <= 10H^7,
hB/l² <= (5/4)*H^7,
eP = C*(1+hB/l+logb(l,hB)) <= 13*C*H^7.
```

The log-base term bound g+1<=H+1 is the source's existing hlogh/hlb, and 1, H <= H^7 for H>=1. Retain flatB<=18H^7, f,r<=2H, m<=H, all relevant source nonnegativity, and the source's split branch formula and non-split branch exclusion. The same multiplication as the source gives

```text
SplitK:
  lenB <= (6H²)*(13*C*H^7) = 78*C*H^9.
not SplitK:
  first term <= 4*C*(2H)*(2H)*(5/4+18)*H^7 = 308*C*H^9,
  second term <= 2*C*(2H)*H*(13*C*H^7) = 52*C²*H^9.
```

Both cases are bounded by (308*C+52*C²)*H^9. Adding the unchanged bbB bound 8*C*H^9 gives P(C)H^9, P(C)=316C+52C². The exact square certificate is

```text
95*(C+1)^2-P(C) = 43*(C-63/43)^2+116/43.
```

All terms are nonnegative. At C=3/2, P=591 while 94*(C+1)^2=1175/2=587.5, so **95 is the least integer coefficient for this refined polynomial envelope**. This is a sharpness statement about the intermediate polynomial, not the arithmetic cost. Other refinements of the prior bounds could reduce the coefficient again.

Hence the proposed conditional replacement for exc_pt is

```text
bbB+lenB(l) <= 95*(C+1)^2*H^9
```

under the same source premises. The argument is a new scalar derivation from those premises and the recovered source helper estimates. No source change or new kernel check.

## 3. Independent E05C paper refinement: 388 to 58 and 1164000 to 11020

With Den<=4H^7+6H^4 (the tighter pre-absorption bound in B11), m>=2 and lStar=m*b/Den>0,

```text
8*b/lStar=8*Den/m <=4*Den <=16H^7+24H^4.
```

Keeping the source bounds on TT, S, etaSz and t gives the more informative cardinality certificate

```text
#exc <= (2H+2)*(8H+16H^7+24H^4+9).
```

Since H>=2, we have 2H+2<=3H, 8H<=H^7/8, 24H^4<=3H^7, and 9<=(9/128)H^7. Thus

```text
#exc <= (7371/128)*H^8 <=58*H^8.
```

The refined scalar estimate is conditional on the actual rank implication H>=m>=2; it does not follow from H>=1 alone. As a check, at H=1 the intermediate product is 228, larger than 58, so the lost premise matters. The bound 58 is not claimed globally optimal for the source domain.

For l in T, l<=3b and log b=g<=H give log l<=H+2<=2H using H>=2. Combining this with Section 2's bound 95 and the nonnegative pointwise costs,

```text
sum_{l in T} log(l)*(bbB+lenB(l))
 <= #T * 190*(C+1)^2*H^10
 <= 11020*(C+1)^2*H^18.
```

The coefficient is 58*190. The exponent 18 remains unchanged. The scalar final product coefficient 11020 is the result of the tighter certificates, not a claim that every intermediate estimate saturates simultaneously. From the already proved big_le_b this term alone is <=(551/200000)*b (11020/4000000=0.002755). The original exceptional estimate would give 291/1000*b. This isolates the exceptional contribution; the remaining prime categories and cohomological terms must still be included before altering aux3.

Retaining the generator term's actual C and cubic power gives, independently from sum_g's earlier hlog and x^C,etaSz bounds,

```text
sum_{l in T subset gset} log(l)*(C*x^C*etaSz)
 <= 2*C*(C+1)*H^3.
```

This can be carried as a separate sharper generator certificate if useful. It does not by itself lower any upstream asymptotic exponent in x.

**Proposed kernel gate:** independently register E05C in bounded parts: polynomial identities and minimum-integer controls (104 from B10; 182/95 here), positive cutoff division and mixed-power estimates, cardinality and finite sum aggregation, generator cubic bound, plus B11's isolated separation and B10's factor-2 row assembly. Keep each module small; no numerical fitting or floating-point maximization necessary.

## 4. New paper math: two-sided band localization

The direct helper `band_small` at [NEqRZeroMulXPow.lean:575–600](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean#L575-L600) bounds C*(4*etaSz+S+g) by w''/8. The next theorem `band_w''` at [NEqRZeroMulXPow.lean:602–630](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean#L602-L630) uses l>=2C, l>=1, bandI=1, and a band witness s in [w'',wB] to conclude w''<=4b/l. Its main source premise is the absolute-error bound on |l*s-b|, with h2, h3, h4 accounting for the three terms at 614–626.

Let y=l*s, b>0, beta=C/l in [0,1/2]. Because eta3<=4etaSz and s>=w'', the same source inequalities imply

```text
|y-b| <= (1/8+beta)*y + beta*b.
```

More generally, for y>=0, b>0, delta>=0, beta>=0 and delta+beta<1, the certificate

```text
|y-b| <= (delta+beta)*y+beta*b
```

is equivalent to the interval

```text
(1-beta)/(1+delta+beta)*b <= y
     <= (1+beta)/(1-delta-beta)*b.
```

Proof: expand the absolute-value upper bound into its two linear inequalities; divide by the strictly positive denominators. Both endpoints satisfy equality in one of the original inequalities. Thus this interval is sharp in the independent scalar domain. With delta=1/8 and beta<=1/2,

```text
(4/13)*b <= l*s <= 4*b.
```

The source upper bound is recovered, with an additional lower bound on the actual witness s. This does not lower-bound every possible w'', since w''<=s. For smaller beta the exact interval retains a tighter two-sided constraint around b. A control at delta+beta=1 (delta=beta=1/2, b=1) allows arbitrary y>=1 and invalidates any finite upper endpoint based on that algebra alone. This is a small independent E05D band-stability proof candidate and useful for interpreting the band approximation as a relative-error certificate.

The same helper window also recovers the scalar scale bound r*eta3<=4*m*w'' at [NEqRZeroMulXPow.lean:632–647](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean#L632-L647), the order-length bound Lw<=C log x at 668–672, and radius inequality k/m<=R0² at 680–685. The proof of three_le_R_zero starts at 687 and runs past this window. These are separate source bounds, not implied by the proposed band interval.

## 5. Bounded read receipt and next source boundary

Two distinct frozen upstream files, **500 returned source lines**:

| Path relative to src/ | Window |
| --- | --- |
| `Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean` | 501–750 (250, cap; Sums section ends at 750) |
| `Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean` | 451–700 (250, cap) |

Previous B10/B11 source windows supply all earlier source anchors, including the denominator and rank envelope, without rereads. No full source scan/build, upstream proof imports, independent kernel proof, GPU/QPU, or paid compute. Runtime/RAM unmeasured.

**Next B13:** preregister `src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean:751–1000` to trace remaining cohomological terms and the actual final aux3 assembly, retaining exact coefficient and eligibility constraints. NEqRZeroMulXPow continuation 701–950 is a distinct dependency window if required. E05A coherence, E05B actual rank/degree-weighted slack, E05C scalar constant/scale refinements and E05D band interval are independent proposed experiments. Global theta-lift multiplicity growth exponent remains UNSOURCED.

# RH-26B-11: denominator, place-weight aggregation and certified refinements

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26B11_REGISTRATION.md](RH26B11_REGISTRATION.md), `ace6f730bdadd503988b6db4ce0aca0021f10522`, before upstream reads.  
**Frozen upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`; observed consolidated main `362d9476fbd4548dead48ed7b6a54600879e1e17`. No equivalence claim.  
**Disposition:** **SOURCE PASS** for Den structure/positivity/cutoff identities, complete AdmT and admitted interfaces, exact etaLoc→etaJ→etaAt→etaSum aggregation, generator-prime alternative, and place-weight denominator. **PARTIAL** for the full numerical aux3 and uniform family export proof, whose ExportBoundOfAdmissible continuation lies beyond line 500. New independent paper certificates; no new kernel run.

## 1. Two different denominators

### 1.1 Cutoff denominator

The source `TwistedPlaces.Den L` is defined at [NEqRZeroMulXPow.lean:257–258](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean#L257-L258), with the equivalent explicit lStar definition at [DataParams.lean:65–69](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/LocalRingCardinality/DataParams.lean#L65-L69). To avoid confusion between the size object L and the auxiliary scale, write g=large2(L)=L.sc.L=x^eps and S=L.Sc. Then

```text
Dcut = n*t²*(N(m)+t)*g² + k*n²*(S+t+g),
lA   = k*g/(m*de2),
lStar = m*b/Dcut.
```

The denominator is positive by the source Den_pos lemma (NEqRZeroMulXPow:271–278); lStar_eq, lStar_pos, lStar_mul_Den and b_div_lStar at 279–301 give lStar=m*b/Dcut, lStar>0, lStar*Dcut=m*b, and b/lStar<=Dcut. The two positive summands are separately bounded after multiplication by lStar by m*b (302–321). lStar<=b/g and lStar<=b, plus log(lStar)<=g, occur at 323–354. The proof retains the additional ParameterChoice' cutoff lower conditions at 355–366, and lA_eq, lA_ge, lA_pos at 368–382.

The registered continuation of Den_le_U at [ExportBoundOfAdmissible.lean:251–262](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L251-L262) completes the scalar upper bound. With H=Ub(L,C)>=1, the source bounds the first summand by 4H^7, the second by 6H^4, then absorbs H^4<=H^7:

```text
Dcut <= 4H^7+6H^4 <= 10H^7.
```

The source's very large scale assumption supplies b>=4*10^6*(C+1)^2*H^18 at [ExportBoundOfAdmissible.lean:283–322](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L283-L322), via exponential scale separation. Then `lA_lt_lStar` at [ExportBoundOfAdmissible.lean:324–388](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L324-L388) bounds lA<=H³ and H³<lStar, retaining the positive denominator and thick density. In particular de2>0 and de2>=x^(-eps), m>=2 are used at 335–360. The next theorem `exc_pt` (391 onward) bounds bbB+lenB at exceptional large primes by 1000*(C+1)^2*H^9; only its setup and part of its length proof through 500 are read. Do not assert completion of its proof or of aux3 in this session.

### 1.2 Place-weight normalization

This is a distinct denominator, the degree of the source number field K=D.what₂.LL over Q. At [TwistedPlaces.lean:314–359](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean#L314-L359), `admissibleMeanCondition_holds` proves TwistedWeightMeanBound. For a rational prime l and w in twAt(L,l), identify its prime ideal q=(D.plEq w).asIdeal, with ramification index e_q and inertia degree f_q. The exact weight identity at 327–339 is

```text
a_w = lwP(w)*ramIdx(w) = log(l)*e_q*f_q/[K:Q].
```

The ideal lies over l by liesOver_resChar (283–312); distinct w map injectively to ideals (340–342). All weights are nonnegative, and the sum of e_q*f_q over all primes above l equals [K:Q]. The twisted support is a subset of that finite domain. Thus the weighted sum over the subset is <=log(l). This is a genuinely normalized degree fraction, and must not be conflated with Dcut.

The companion result in MemPrimesOverOfMem at 64–67 and 205–245 bounds local-degree sums in the host field D.host.E (degree 2*f) rather than in K. nLam is the product of local ramification and inertia degrees, each positive. Its successor version begins 246; proof continues after the present file boundary. Keep those two number fields distinct.

## 2. Full local admissibility and family entry condition

The remainder of TwistedPlaces.lean has now been read to EOF (365). At [TwistedPlaces.lean:251–279](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean#L251-L279):

- RamifiedPrimeLengthBound controls sumOver(len)+BB by midG for q or d, and midG by 2*C*f*m*b.
- GeneratorPrimeEtaBound separately bounds etaAt by log(l)*dZ0(j)*(gcost+gs+VVr+vhE+epsL) on gset; gcost<=C*x^C*etaSz.
- TwistedWeightMeanBound is the sum-of-place-weights <=log(l) assertion, for rational prime l.
- ParametersPolynomiallyBounded retains CLw,CYL<=C, k,n,t<=x^C, de2>=x^(-eps), log(hE)<=C*x^C, log(restRowsFiniteGroupCard)<=C*x^C*g.
- AdmT is precisely the conjunction of the seventeen conditions in the constructor recovered in B09: adm1, adm2, adm3, ArchimedeanSignatureMatching, adm5, adm6, admA, admB, MediumInertPrimeLengthBound, SmallInertPrimeSmallOrderLengthBound, BandPlaceWeightApproximation, LargePrimeLengthVanishing, ExceptionalPrimesBounded, SmallPrimeLengthBound, RamifiedPrimeLengthBound, GeneratorPrimeEtaBound, ParametersPolynomiallyBounded.

At [TwistedPlaces.lean:361–361](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean#L361-L361), admitted L P C means ShaFinOdd D → exists tb, AdmT L tb C P. The normalized place-weight mean is proved separately, rather than being an extra field in AdmT. This matches B10's family-level interface.

## 3. Exact aggregation supplier: etaAt_le and etaSum_eq_sum

The critical implementation is in `src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean`, a direct dependency of the B10 rank helper. The new source read recovers three actual theorems.

1. **etaSum_eq_sum** at [MemPrimesOverOfMem.lean:92–103](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean#L92-L103) rewrites the total etaSum as the finite sum of etaAt over the image of the twisted support under residue characteristic. It uses finite fiberwise summation, so each support place is counted once. No summability assumption is needed for this finite regrouping.
2. **etaAt_le** at [MemPrimesOverOfMem.lean:105–154](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean#L105-L154): for eligible j, l outside gset and U>=0, assume adm1, adm2, adm3 and a pointwise uniform coefficient bound vcc(i,pi)+padicValNat(l,restRowsFiniteGroupCard)<=U at twisted i with D.nd.l i=l and good pi. Then

```text
etaAt(L,j,l) <= log(l)*(dZ0(j)*U).
```

The proof first fixes w in twAt(L,l). The source identity `D.etaJ_tie j w` at 115 rewrites etaJ(j,w) as the sum of etaLoc over locs(j,w), with j-range obligations. The equality D.nd.l i=l for each selected i is established at 123 using D.nd.w_l i, locs_mem and the residue characteristic of w. This **closes the individual eligibility link** previously retained as an explicit extra assumption in B10. The inequalities 117–138 apply adm1 to each local term, replace each good-point coefficient by U using nonnegative multiplicities, sum, and apply adm2 and adm3. This gives etaJ(j,w)<=dZ0(j)*U. The proof then multiplies by nonnegative a_w and sums (139–147); the empty twisted-support case is explicit (148–151). In the nonempty case l is prime, and the normalized degree budget gives the result (152–154). U>=0 is essential when replacing the total multiplicity or total weight by its cap.
3. **etaAt_le_g** at [MemPrimesOverOfMem.lean:156–166](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean#L156-L166) handles generator primes independently using GeneratorPrimeEtaBound and the second adm6 clause:

```text
etaAt(L,j,l) <= log(l)*dZ0(j)*
 [C*x^C*etaSz+2/l²+VVr(D,l)+vhE(D,l)].
```

The non-generator multiplicity route is not applied to these exceptional generator primes. The final aux3 arithmetic summation, including infinite vvTerm/ShaFinOdd and exceptional-prime count treatment, is beyond the registered ExportBoundOfAdmissible window. The source bridge itself is exact.

## 4. New paper theorem: split the discarded budget into two certified defects

Let l be a non-generator rational prime, j an eligible lift, and use the actual finite set W=twAt(L,l), R=dZ0(j)>=0, and U>=0 from etaAt_le. For every w, write I_w=locs(j,w), M_i=sum_pi mult(i,pi), and d_i=dM(i). B08 establishes M_i<=d_i; adm2/adm3 give sum M_i<=R on each I_w. The source etaJ_tie now gives exactly etaJ(j,w)=sum_i etaLoc(i) (not an independently invented global objective).

Assume the B10 coefficients E_i bound each good-point valuation-plus-group correction, so etaLoc(i)<=M_i*E_i. All multiplicities are nonnegative; E_i may be signed. For any choice of lambda_w>=0, E04C's verified generic dual bound yields the independent consequence

```text
B_w(lambda_w) = lambda_w*R + sum_{i in I_w} d_i*max(E_i-lambda_w,0),
etaJ(j,w) <= B_w(lambda_w).
```

Combining with the original uniform bound etaJ(j,w)<=B:=R*U gives etaJ(j,w)<=min(B,B_w). Thus

```text
etaAt(L,j,l) <= sum_w a_w*min(B,B_w).
```

Define the degree coverage alpha_l=sum_{w in W} e_w*f_w/[K:Q], so 0<=alpha_l<=1 and sum a_w=alpha_l*log(l). (For empty support alpha_l=0.) Since min(B,B_w)=B-max(B-B_w,0), the new certified upper bound can be written exactly as

```text
etaAt(L,j,l)
 <= log(l)*B
    - log(l)*(1-alpha_l)*B
    - sum_w a_w*max(B-B_w,0).
```

The first discarded-budget term is **degree coverage slack**. The second is **local multiplicity-cap slack** relative to the uniform envelope. Both are nonnegative. This is a stronger conditional scalar bound for the actual source etaAt, with generator primes handled separately. The finite prime regrouping etaSum_eq_sum supports summing these nonnegative improvements over eligible non-generator primes while retaining the source's generator bounds. No conclusion about a better asymptotic aux3 exponent is justified until the final prime-wise envelopes and their dependence on x are checked.

The cap bound only uses lambda_w>=0 and finite nonnegative masses/caps; no choice of actual arithmetic multiplicities is free. The original U may itself depend on admissibility and prime class. A useful implementation takes E_i=min(U, E_i_local) when both are valid upper bounds, then uses a supplied lambda_w; the verified E04C bound certifies it without a greedy-existence claim. The proof's original U>=0 premise remains for B and coverage slack. The new result is paper algebra combining source contracts and an independently verified theorem, not a new kernel proof of the combined source-like contract.

**Exact scalar fixture.** Factor log(l) out of the weight. One selected place above a rational prime has e*f=2 in a degree-4 field, hence coverage 1/2. Let R=2,U=9, local caps (1,3), coefficients (9,2), lambda=2. Then B=18, B_w=11, and the proposed bound is (11/2)*log(l), compared with 18*log(l) in the original uniform/full-coverage envelope. The discarded budget is (9+7/2)*log(l): 9 from coverage and 7/2 from caps. This is a scalar model of the sourced normalization, not an exhibited host/family. If the cap on the high coefficient is dropped, masses (2,0) can yield 18, invalidating the bound 11. If weight sum exceeds log(l), the coverage slack can be negative; no improvement certificate follows. Signed weights also invalidate monotone aggregation. These give useful independent adversarial controls.

**Proposed E05B kernel contract:** finite nested sums, local pointwise majorants, nonnegative multiplicities, local caps and per-place rank budgets; combine E04C weak duality with exact min/hinge and weighted coverage decomposition. Verify ordinary, zero-budget, empty-support and signed-weight/missing-cap controls. Use the actual per-place degree factor in an independent scalar normalization theorem with positive degree and nonnegative prime-log weight. Keep the number-field realization an explicit external premise. Optional stronger output: sum per-prime improvement over a finite support image while preserving distinct generator cases.

## 5. Independent cutoff refinement for E05C

The actual denominator and its two source component bounds also yield a smaller scalar threshold for the isolated lA<lStar separation problem. With H>=1, m>=2, de2>=1/g>0, k,g<=H and Dcut<=4H^7+6H^4:

```text
lA <= k*g²/m <= H³/m,
lStar = m*b/Dcut.
```

The exact equivalence for positive m,de2,Dcut is

```text
lA < lStar  iff  k*g*Dcut < m²*de2*b.
```

In particular the sufficient condition

```text
b > (4H^10+6H^7)/m²
```

gives strict separation, and the simpler sufficient threshold b>H^10+(3/2)H^7 follows using m>=2. This retains the factor m in both cutoffs instead of absorbing it early. The source actually proves a much larger b lower bound for other purposes, so this is a reduction of the **isolated separation gate**, not a recommendation to weaken every large-scale hypothesis in the export proof. Equality at b=k*g*Dcut/(m²*de2) makes the two cutoffs equal, furnishing the sharp scalar boundary control. No assumption of family existence or alteration of its parameters. The more precise denominator envelope also yields lStar>=m*b/(4H^7+6H^4) for b>=0. Add these exact scalar statements to the future E05C constant-refinement experiment; keep B10's 104/2 constants separate from this scale threshold.

## 6. Read receipt and next source boundary

Five distinct source files, **1115 returned lines** at the frozen pin:

| Path relative to src/ | Window |
| --- | --- |
| `Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean` | 251–500 (250, per-file cap; exc_pt proof continues) |
| `Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean` | 251–365 (115; EOF) |
| `Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean` | 1–250 (250; cap) |
| `Formalism/LocalRingCardinality/DataParams.lean` | 1–250 (250; cap) |
| `Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean` | 201–450 (250; cap) |

The two continuation windows and direct import DataParams, prior direct import NEqRZeroMulXPow and its MemPrimesOverOfMem import are within the registered dependency limit. Prior B08–B10 anchors reused without source rereads. No full source scan/build, copied upstream proof, independent kernel run, GPU/QPU, or paid compute. Runtime and RAM unmeasured.

**Next B12:** freshly preregister `src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean:501–750`; inspect the remainder of exc_pt and subsequent prime-wise/global sum assembly. If needed continue in a later fresh 250-line window; TwistedPlaces.lean is fully inventoried across B10/B11. Follow actual named helpers only. The etaAt aggregation is now established; final aux3/uniform-export supplier still PARTIAL. Alternatively independently register E05B (exact weighted coverage and capped multiplicity slack), E05C (104/2 and cutoff thresholds) or E05A coherence defect. The global theta-lift multiplicity growth exponent remains UNSOURCED.

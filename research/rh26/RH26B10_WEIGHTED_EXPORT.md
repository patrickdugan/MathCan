# RH-26B-10 — rank-weighted local objective, family export interface, and sharper constants

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26B10_REGISTRATION.md](RH26B10_REGISTRATION.md), commit `06640a423551843a7331ec69ff82ab32597995c4` before new upstream reads.  
**Frozen upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`; observed consolidated main `362d9476fbd4548dead48ed7b6a54600879e1e17`. No equivalence claim.  
**Disposition:** **PASS for exact local weighted observable and capacity normalization, final aux3 target and family interface, logarithm-weighted small-prime estimates. PARTIAL for their actual full downstream assembly.** The export implementation hit its 250-line boundary within Den_le_U. The exact Den definition and global summation proof remain uninspected. Three independent paper refinements below; no new kernel run. No global theta-lift multiplicity exponent claim.

## 1. Actual weighted observable and rank normalization

The exact source definitions are now recovered in [TwistedPlaces.lean:161–195](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean#L161-L195):

- `adm1 D` at 171–174 bounds `etaLoc i` for twisted local indices i with l=D.nd.l i outside gset D by the finite sum over good pi of
  `mult(i,pi) * (vcc(i,pi) + padicValNat l restRowsFiniteGroupCard)`, with real casts.
- `adm2 L` at 176–178 requires, for each eligible lift j and twisted place w whose residue characteristic is outside gset, that the sum of all good-point multiplicities over locs(j,w) be at most `zeroSpaceRankAtPlace j w`. B09 verified that this field is supplied directly by MultLe; here its extra non-generator condition is explicit.
- `adm3 L` at 180 identifies `zeroSpaceRankAtPlace j w = dZ0 j` for every eligible lift and twisted place.
- `ArchimedeanSignatureMatching` at 182–185 bounds vcc on twisted non-generator good points by s + sumOver(len) + VVr + vhE + BB + epsL.
- `adm6` at 192–195 bounds s+epsL by nuL+2/l² and separately gs+epsL by 2/l² on generator primes.

This closes the local observable question raised in B09. The actual local etaLoc is a weighted valuation sum upper bound, not just an independently proposed signed residual. The new weighted certificate in Section 4 gives a conditional direct estimate of this actual observable.

### Exact target of the export

At [TwistedPlaces.lean:136–165](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean#L136-L165), the source defines

```text
etaSum(L,j) = sum_{w in supp, muAt(w) != mu0}
              lwP(w) * ramIdx(w) * etaJ(j,w)

etaAt(L,j,l) = sum_{w in twAt(L,l)}
              lwP(w) * ramIdx(w) * etaJ(j,w)

vvTerm(D,l) = if l is prime then
              (sum_{1<=e<t} shaLen(l,e)) * log(l)
              else 0.
```

The finite set twAt is the twisted support at residue characteristic l. The source casts the finite shaLen sum from rationals to reals. `aux3(L,C)` (161–165) assumes ShaFinOdd and Summable(vvTerm D), and for each eligible lift j asks for

```text
etaSum(L,j) <= dZ0(j) *
  [ C*(f*m*b*large2(L)^2 + (log x)^2*Nc) + tsum_l vvTerm(D,l) ].
```

Here large2=L.sc.L (61), and the previously inspected source uses large2=x^eps (see NEqRZeroMulXPow.lean:138–140). We do not replace the summability hypothesis by a finite-support assumption. The specific conversion from the finite local etaLoc terms to the place-weighted etaJ terms, the handling of generator primes, and all denominator cancellation in the global proof have not yet been inspected. Do not identify the local upper estimate with the entire aux3 expression.

The family declarations at [ExportFamilies.lean:49–66](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/StatementFamilies/ExportFamilies.lean#L49-L66) make the uniformity requirement explicit. AdmFC(Fm,Ca) is eventual admitted data at all eligible family indices, with one constant Ca. FamilyThinScalesBound(Fm,C) and OrbitValuationBound are eventual aux3 results. UniformExportStatement(eps) sends any input Ca to an output C valid for every family with that input bound. KudlaFamilyStatement maps AdmF to OrbitValuationBound; the wrapper uses the uniform export and existential choices. This is the exact family-level *contract*. Its supplying proof and the final LinkN adapter remain deeper source work.

## 2. Row bounds and the admissible table

The precise data fields of Tab at [TwistedPlaces.lean:126–133](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean#L126-L133) are s, len, BB, band, exc, gcost, gs. The source keeps the columnwise length conditions distinct from the pointwise local total (B09).

At [TwistedPlaces.lean:200–232](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean#L200-L232), admA is a total place-length bound for eligible split primes at least 5 with the window/exception condition; the right side has factors `(2*nLam*m+1)*eP`. admB is a per-place estimate for inert primes below lA with large order, involving `C*(nLam+1)*r` and powers of l−1, plus GP and large2. MediumInertPrimeLengthBound and SmallInertPrimeSmallOrderLengthBound are per-place estimates involving hB/l², flatCD and eP, with different prime/size/order eligibility. BandPlaceWeightApproximation gives a real s in [w'',wB] with an explicit error on |l*s−b|. Here nLam is local degree (94), eP=C*(1+hB/l+log_b(l,hB)) with the source expression `Real.logb l (hB L)` (69), hB=b+Sc+etaSz+t+2 (63), flatCD=(wP+eta3)/l+Sc+large2+eta3*indicator(band) (213–214). The notation for eP is a base-l logarithm of hB, not log base b.

`localBoundTableAllPrimes_rowsAndBand` at [LocalBoundTableAllPrimesRowsAndBand.lean:49–66](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesRowsAndBand.lean#L49-L66) transfers the length function from tabX to tab when l!=3 and RangeAD holds, and sets it to zero outside RangeAD for l!=3. The source excludes 3 from the inert cases using h.small. The proof establishes nonnegativity of the right-hand-side quantities (67–97), and derives the four row bounds from existing numerical row hypotheses or the zero-length branches (98–152); band approximation is inherited at 153. Therefore replacing the table columns with a joint-maximizer allocation may break these per-place conditions. A smaller *scalar* local sum envelope requires no such change of columns.

The definitions of large-prime vanishing, exceptional-prime cardinality/size, small-prime bound and midG at [TwistedPlaces.lean:234–249](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean#L234-L249) preserve the source's exceptions and scale. The AdmT tuple itself is not reached by this window (next range TwistedPlaces.lean:251–500).

## 3. Export scale and actual logarithmic prime sum

The inspected part of `ExportBoundOfAdmissible.lean` contains a concrete theorem `sum_small` at [ExportBoundOfAdmissible.lean:61–62](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L61-L62):

```text
sum_{l in T} log(l) * (bbB(L,C)+lenB(L,C,l))
 <= 1000*(C+1)^3 * f*m*b*large2(L)^2
```

under C>0, ParameterChoice', ParametersPolynomiallyBounded, Large, and a finite prime set T with l!=2,3 and l<=lStar. The proof separates bb, eP, three row classes and flat errors; it uses `lenB_split`, `sum_bb`, `sum_eP`, `sum_rowb`, `sum_rowc`, `sum_rowd`, and `sum_flat` ([ExportBoundOfAdmissible.lean:63–122](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L63-L122)). These named suppliers' full statements/bodies have not all been opened; the scalar assembly is directly visible. This is an actual logarithm-weighted prime sum, separate from the multiplicity-weighted etaLoc sum.

The export introduces `Ub(L,C)=x^(C+2)*exp(x^(eps/4))` at [ExportBoundOfAdmissible.lean:138–151](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L138-L151) and bounds x^C, 1, x, exp(x^(eps/4)), etaSz and Sc by Ub (Sc by 4*Ub), see 145–200. The ranks_le_U theorem at 202–234 bounds n,k,t,m by Ub, f,r by 2Ub, and N(m)+t,nV by 4Ub². Den_le_U begins at 236 with target Den(L)<=10*Ub^7; only its setup through line 250 is read. **Den definition and proof completion are not recovered.** The direct import NEqRZeroMulXPow has rank and scale inequalities (63–130,138–190), including f=2n, m<=k, r<=2k, t>=r+5, b=exp(large2), b'=xb/X', etaSz<=b', Sc<=b'; 190–200 starts a further bT bound. Its next window is 201–450.

## 4. Independent extension E05B: a certificate for the actual local etaLoc sum

Fix an eligible j and a twisted w with residue characteristic outside gset D. Let I be a finite subset of locs(j,w) whose individual local primes l_i are outside gset. Explicitly retain this individual eligibility condition until the source l_i-to-resChar(w) link has been traced. By TwPl.twLoc (TwistedPlaces.lean:120–124), these indices are twisted. Let

```text
M_i = sum_{pi in Zgood(i)} mult(i,pi) >= 0,
u_i = dM(i),
R = dZ0(j).
```

The prior B08 source proves M_i<=u_i (GoodPointMultiplicityLeRankProof.lean:82–100), and the new adm2/adm3 statements yield sum_{i in I} M_i<=R (nonnegative multiplicities justify restricting to the subset). Using adm1, ArchimedeanSignatureMatching and the first adm6 field, define the actual uniform coefficient

```text
E_i = sumOver(D,l_i,tb.len i) + tb.BB i
      + VVr(D,l_i) + vhE(D,l_i) + nuL(D,l_i)
      + 2/l_i² + padicValNat(l_i, restRowsFiniteGroupCard).
```

For every good pi, vcc(i,pi)+padicValNat(...)<=E_i. Multiply by its nonnegative multiplicity and sum; adm1 gives etaLoc(i)<=M_i E_i. For *any supplied* nonnegative weights a_i, including a log weight when its sign and eligibility are proved, summing yields

```text
sum_{i in I} a_i etaLoc(i) <= sum_{i in I} M_i (a_i E_i)
 <= lambda*R + sum_{i in I} u_i max(a_i E_i - lambda,0), lambda>=0.
```

The last step is precisely the independently kernel-verified E04C dual theorem under its hypotheses. This is a new conditional source-anchored paper application to **the actual etaLoc observable**, replacing B09's independently defined residual by the real source local target. It applies to a supplied host satisfying the named premises, not to a freely chosen automorphic family. No sign hypothesis on E_i is needed; nonnegative a_i and M_i are essential. The new application as a combined theorem has not been kernel-checked. The dM cap comes from the B08 theorem, not adm2 alone.

A minimal control: two local indices have multiplicity masses capped by 1 and 3, joint budget R=2 and coefficients 9 and 2 (a_i=1). lambda=2 yields a bound 2*2+1*(9-2)=11, attained by masses (1,1), whereas the maximum-only bound is 18. This is an independent scalar fixture, not instantiated arithmetic data. Dropping the individual cap permits all mass on coefficient 9 and breaks the bound 11. Negative a_i invalidates multiplication of the etaLoc inequality in general (e.g. etaLoc=0, M_iE_i=1, a_i=-1).

If all E_i have a common additive correction B_l and all a_i=a>=0 at one place, the correction can be pulled into a separate a*R*B_l when B_l>=0. The exact equal-prime/grouping and nonnegative-weight premises must be proved before specializing. The source's global etaSum uses a different place weighting; Section 1 identifies the missing etaLoc-to-etaJ relationship, so no claim of improved aux3 follows yet.

## 5. Independent constant improvements (paper algebra)

### A. Reduce the polynomial envelope 1000 to 104 in sum_small

The source assembly at [ExportBoundOfAdmissible.lean:96–122](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean#L96-L122) uses X=f*m*b*large2²>=0 and the polynomial

```text
P(C) = C + 11*C*(3+2*C) + 80*C + 64*C + 32*C
          + 4*C*(102+4*(2*C+1)^2)
     = 64*C³ + 86*C² + 634*C.
```

Its hK upper-bounds P(C) by 1000*(C+1)^3. For C>=0 the following independently derived exact identity proves a tighter envelope:

```text
104*(C+1)^3 - P(C)
 = 40*(C-3/5)^2*(C+6/5)
   + 226*(C-697/1130)^2 + 4159/5650.
```

Every term is nonnegative; indeed the last is positive. Hence replacing only hK by this inequality gives the conditional source-strengthening `sum_small <= 104*(C+1)^3*X` from the same preceding component estimates. The least **integer** coefficient for the displayed polynomial envelope is 104: at C=3/5, P=53148/125, (C+1)^3=512/125, and 103*512=52736<53148. This lower control concerns the assembled polynomial upper envelope, not a lower bound on the actual arithmetic prime sum; tighter component estimates may improve the constant further. No upstream source changes and no new kernel proof yet.

### B. Reduce the final 8 to 2 in sum_row_small_le

At [SmallSum.lean:106–158](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CyclotomicBounds/SmallSum.lean#L106-L158), the source bounds a small-prime sum over prime factors of Q or 3, under Q!=0, Q<=n², x>=1, C>0, n<=x^C, (C+3)^2*(1+log x)^2<=L, x^C*L<=b, fm>=1. Its conclusion is

```text
sum_l log(l)*(C*fm*b*log x + C*x^C*L²)
 <= 8*C*fm*b*L².
```

The final two terms are separately bounded by C*fm*b*L² in t1 (138–141) and t2 (142–150), with the logarithm-sum comparison at 152–157. Their sum is bounded by **2*C*fm*b*L²** directly, retaining every source hypothesis. This is a paper-algebra tightening of the final assembly, not a new asymptotic estimate or independent proof of the earlier number-theoretic lemmas.

The source's exact elementary logarithm budget appears at [SmallSum.lean:55–104](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CyclotomicBounds/SmallSum.lean#L55-L104): product of distinct prime divisors divides N, hence sum log l<=log N; with the extra prime 3 the bound is log Q+2, then <=2C log x+2 under Q<=n² and n<=x^C. The elementary assembly improvements may be tested in a small independent E05C real algebra module; upstream stronger statement remains proposed.

## 6. Read receipt and next checkpoint

Six source files, **1105 returned lines**:

| Path relative to src/ | Window |
| --- | --- |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesRowsAndBand.lean` | 1–155 (155; EOF) |
| `Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean` | 1–250 (250; cap, Den_le_U starts at 236) |
| `Formalism/SharpRestriction/LevelLetterCocycles/NEqRZeroMulXPow.lean` | 1–200 (200) |
| `Formalism/SharpRestriction/LevelLetterCocycles/StatementFamilies/ExportFamilies.lean` | 1–90 (90; EOF) |
| `Development/AutomorphicArithmetic/CyclotomicBounds/SmallSum.lean` | 1–160 (160; EOF) |
| `Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean` | 1–250 (250; cap) |

All source reads pinned; direct imports and one further import only. B08/B09 anchors reused without rereads. No full scan/build, independent Lean run, GPU/QPU or paid compute. Runtime/RAM unmeasured.

**Next B11:** preregister exact continuation `src/Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean:251–500` and `src/Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean:251–500`; recover Den and AdmT/admitted definitions, the export proof's place aggregation, and the actual etaLoc-to-etaJ identification if present. If Den or the final assembly is outside those windows, record next exact path/range. E05A max-sum coherence, E05B actual etaLoc capacity bridge and E05C polynomial/constant refinement remain separately registered future checks. Global theta multiplicity growth exponent remains UNSOURCED.

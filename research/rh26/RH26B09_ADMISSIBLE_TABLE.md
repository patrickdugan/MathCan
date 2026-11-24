# RH-26B-09 — admissible local tables, suprema, and coherence defects

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26B09_REGISTRATION.md](RH26B09_REGISTRATION.md), commit `5729e89e635d255dadba6985d663f51326178ab7`, before new upstream source reads.  
**Frozen upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`. Consolidated main observed `362d9476fbd4548dead48ed7b6a54600879e1e17`; no equivalence claim.  
**Disposition:** **PASS for the exact table constructor, direct MultLe use and piecewise pointwise bound; PARTIAL for downstream weighted summation.** The full AdmT-to-LinkN numerical export has not been reopened. E04C repair audit is independent and pending at time of source trace. New math below is paper derivation, no new kernel result.

## 1. The local rank budget survives intact

The exact theorem `GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion` at [AdmittedStatementsOfLocalBoundsConclusion.lean:53–64](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmittedStatementsOfLocalBoundsConclusion.lean#L53-L64) takes Concl L P X C and produces an existential tb : TwistedPlaces.Tab L with AdmT L tb C P.

It extracts tf and the two/three-place and small-prime certificates from h.two, then chooses tb=tab L X tf C. Its line 58 constructs **TwistedPlaces.adm2 L** directly from h.mult j hj w hw; the additional argument to adm2 is unused in that lambda. This is the precise conversion from the B08 good-point multiplicity theorem to the admissible table. The full independent definition of adm2 has not been inspected here.

The proof separately invokes the archimedean-signature pointwise match, adm5, adm6, row and band certificates, large-prime vanishing/exceptional-set results, small/ramified-prime length bounds, generator-prime eta bounds, and parameter bounds. The returned tuple at lines 62–64 keeps all these fields. MultLe is a capacity field in this package, rather than itself a weighted estimate.

## 2. Pointwise error table

The wrapper at [AdmissibleTableOfLocalBoundsStatement.lean:45–46](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleTableOfLocalBoundsStatement.lean#L45-L46) delegates to `GlobalTheory.NLink.admissible_table_of_conclusion` at [AdmissibleTableOfLocalBounds.lean:77–88](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleTableOfLocalBounds.lean#L77-L88). This yields TwistedPlaces.ArchimedeanSignatureMatching L (tab L X tf C) from the bundled Concl and a uniform small-prime/3 bound. The proof works for a twisted local index i, a prime outside the generator set, and a good point pi.

Write l=D.nd.l i, p_i(pi)=vcc(i,pi), s_i(pi)=sPi(...), and c_l=VVr(D,l)+vhE(D,l)+epsL(l). Using the prior B07 definitions of Bd and tab ([BoundAtTwoThreeFamily.lean:52–54](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L52-L54), [BoundAtTwoThreeFamily.lean:135–148](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L135-L148)), the local conclusion has the scalar form

```text
p_i(pi) - s_i(pi) - c_l
   <= sum_{v above l} tb.len(i,v) + tb.BB(i).
```

The table cost on the right has different constructions. The complete case proof is in [AdmissibleTableOfLocalBounds.lean:89–153](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleTableOfLocalBounds.lean#L89-L153).

| Eligible branch (in source order) | Length table | BB term |
| --- | --- | --- |
| l in small | zero | sumOver(tf.len i)+tf.BB i |
| l=3, outside small | constant (sumOver(tf.len i)+tf.BB i)/ncard(placesOver E 3) | zero |
| l=q or l=d | zero | midG L C l |
| RangeAD L X.exc l | lenR X.len0 i (pointwise sup over good pi) | supZ i (X.errorBoundHub i) |
| otherwise (large, outside exception) | zero | zero |

In the 3-branch at [AdmissibleTableOfLocalBounds.lean:102–118](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleTableOfLocalBounds.lean#L102-L118), the source proves finiteness and nonemptiness of places above 3, derives a strictly positive real cardinality, and cancels the denominator in the constant sum. This is a mass-conserving redistribution. The common helper `sumOver_const` at 55–59 needs a nonzero rational prime index (formal premise l≠0); `sumOver_mono` at 61–65 transfers a pointwise inequality to that finite place sum.

The medium RangeAD branch at [AdmissibleTableOfLocalBounds.lean:128–143](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleTableOfLocalBounds.lean#L128-L143) is stronger before the final table domination. From hC.mid it obtains the point-specific Bd cost

```text
b_i(pi) = sum_{v above l} X.len0(i,pi,v) + X.errorBoundHub(i,pi).
```

Then it upper-bounds each summand and the hub error separately by its supremum over good pi (helper le_supZ, lines 67–71). This permits a single table row independent of pi. It also discards information about whether the same point simultaneously realizes those suprema.

## 3. Numerical side conditions actually read

- `GlobalTheory.NLink.adm5_tab` at [LocalBoundTableAllPrimesSizeConditionFive.lean:47–65](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesSizeConditionFive.lean#L47-L65) discharges the non-small/non-q/non-d error budget using h.bb. The nonnegative bound in its proof is C*f*n*t^2*nV*large2(L)^2. The proof checks the RangeAD branch, uses the finite supremum bound when good points are nonempty, and uses zero in the empty/outside-range cases. The wrapper at [LocalBoundTableAllPrimesSizeConditionFiveStatement.lean:45–46](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesSizeConditionFiveStatement.lean#L45-L46) is exact.
- `GlobalTheory.NLink.adm6_tab` at [LocalBoundTableAllPrimesSizeConditionSix.lean:47–62](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesSizeConditionSix.lean#L47-L62) supplies two small-error conditions. One uses h.kill and epsL(l)=1/l^2 to obtain sPi+epsL(l) <= 2/l^2; the other is the exact identity epsL(l)+epsL(l)=2/l^2. The wrapper is [LocalBoundTableAllPrimesSizeConditionSixStatement.lean:45–46](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesSizeConditionSixStatement.lean#L45-L46). Neither result converts MultLe into a global weighted sum on its own.
- The row/band wrapper at [LocalBoundTableAllPrimesRowsAndBandStatement.lean:45–46](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesRowsAndBandStatement.lean#L45-L46) supplies the five predicates admA, admB, MediumInertPrimeLengthBound, SmallInertPrimeSmallOrderLengthBound, BandPlaceWeightApproximation. Its implementation is a precise new source lead: `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesRowsAndBand.lean`. The full definitions and downstream weighted export are not included in this run.

## 4. Independent extension A: a maximum-coherence defect

Consider finite nonempty good-point set J and finite nonempty coordinate set K. Take arbitrary real numbers h_(pi,k), where K includes the places over l and a separate hub-error coordinate. Define

```text
U = sum_k max_pi h_(pi,k)
M = max_pi sum_k h_(pi,k).
```

The RangeAD source uses the separate-coordinate envelope U. A joint maximum M is a pointwise upper bound on the original b_i(pi) and satisfies M<=U. Define the coherence defect

```text
U-M = min_pi sum_k [max_r h_(r,k) - h_(pi,k)] >= 0.
```

This identity follows by subtracting each point's total from the fixed U. Every bracket is nonnegative, and finite extrema are attained. Equality U=M holds exactly when at least one point attains every coordinate maximum simultaneously (if K is empty the condition is vacuous; J nonempty still required). This algebra is valid with signed entries.

For nonnegative entries, let p=|J| and k=|K|. Then

```text
M <= U <= min(p,k)*M.
```

Proof: U<=sum_pi sum_k h_(pi,k)<=p*M by nonnegativity; every individual coordinate maximum is <=M, hence U<=k*M. Both estimates are sharp: a square diagonal table of ones has U=k and M=1. A two-place example with rows (1,0),(0,1) has U=2 and M=1. Separate maxima have no common witness. Signed entries can invalidate the multiplicative upper bound: rows (1,-1),(-1,1) give U=2 and M=0, while the additive defect remains valid.

**Candidate E05A:** independently prove finite maximum/sum interchange inequality, attained defect identity, common-maximizer equality characterization, nonnegative multiplicative bound, and exact diagonal/signed controls. Then quantify the tradeoff between retaining joint local error and the source's required coordinatewise length bounds. A smaller M is not automatically a replacement for the source table because admA, admB, length bounds and further admissibility conditions may constrain individual columns. The candidate theorem only certifies the total pointwise error.

## 5. Independent extension B: connect the recovered rank budget to a weighted bound

The actual B08 source gives two compatible budgets: at [GoodPointMultiplicityLeRankProof.lean:82–100](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L82-L100), each local i has M_i=sum_{pi good} mult(i,pi)<=dM(i); at [GoodPointMultiplicityLeRankProof.lean:106–149](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L106-L149), for eligible fixed (j,w), the total of these masses over locs(j,w) is <=R=zeroSpaceRankAtPlace(j,w). These are nonnegative natural multiplicities cast to reals.

For a finite subset of those i to which the non-generator pointwise bounds apply, write

```text
M_i = sum_pi mult(i,pi)
q_i(pi) = vcc(i,pi)-sPi(i,pi)-VVr(l)-vhE(l)-epsL(l).
```

Use a finite scalar coefficient E_i bounding q_i(pi) for all good pi. In the medium branch take E_i=max_pi b_i(pi) when good pi is nonempty; in uniform branches take the actual common local bound, and set E_i=0 for an empty good-point set. The available source inequalities yield

```text
sum_i sum_pi mult(i,pi)*q_i(pi)
    <= sum_i M_i E_i.
```

All masses are nonnegative and sums are finite. The total budget remains valid on the chosen subset by nonnegativity. The local dM cap and joint zero-space rank budget now give the following **independent conditional paper bound**, using the E04C algebra for every lambda>=0:

```text
sum_i sum_pi mult(i,pi)*q_i(pi)
    <= lambda*R + sum_i dM(i)*max(E_i-lambda,0).
```

For a single coordinate lambda=max(0,max_i E_i), this recovers the crude R*lambda bound; minimizing over lambda can exploit the individual caps. This is a concrete source-anchored *candidate application* of the weighted allocation abstraction because the actual dM and rank capacities have been recovered. The weighted residual on the left is our independently defined observable, not yet identified as the precise downstream objective of the upstream proof. No new source claim of that identification, no global summation/exponent, and no claim that actual multiplicities may be freely optimized. The tighter local joint maximum requires the nonempty finite set and appropriate pointwise source hypotheses.

## 6. Next source and experiments

**B10**: preregister a fresh bounded read of `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesRowsAndBand.lean`, with targeted follow-up to the definitions of TwistedPlaces.AdmT and its export in `Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean` (direct import previously observed in LinkNAlongFamilyOfLocalBounds.lean:6). Trace the actual rank-weighted sum, coefficients, prime weights and denominator before asserting equivalence to Section 5. Stop at a precise source boundary if the definition is elsewhere. **E05A**: coherence-defect kernel experiment; optionally E05B combine B08 local and global budgets with E04C weighted certificates after its kernel gate passes. B09 does not settle the global theta multiplicity exponent.

## 7. Bounded read receipt

Eight source files, **536 returned lines**:

| Path relative to src/ | Window |
| --- | --- |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmittedStatementsOfLocalBoundsConclusion.lean` | 1–66 (66) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleTableOfLocalBoundsStatement.lean` | 1–46 (46) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesSizeConditionFiveStatement.lean` | 1–46 (46) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesSizeConditionSixStatement.lean` | 1–46 (46) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleTableOfLocalBounds.lean` | 1–155 (155) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesSizeConditionFive.lean` | 1–67 (67) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesSizeConditionSix.lean` | 1–64 (64) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalBoundTableAllPrimesRowsAndBandStatement.lean` | 1–46 (46) |

Direct imports and their implementations only, two dependency hops. Previously read B07/B08 definitions and proof anchors were reused without source rereads. No full upstream scan/build, copied upstream proof, new independent kernel run for these derivations, GPU/QPU, or paid compute. Runtime/RAM unmeasured.

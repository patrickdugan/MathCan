# RH-26B-08: exact local multiplicity theorem and independent capacity certificates

**Date:** 2026-11-24 (Asia/Manila).  
**Registration:** [RH26B08_REGISTRATION.md](RH26B08_REGISTRATION.md), commit `10a3cfd06bbe262e06b05f5867ef58883c15e0bd` before new source reads.  
**Immutable upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`. Observed consolidated main `f38c099ec6017a3ce839cba4e06857eda6c9a057`; no equivalence claim.  
**Disposition:** **PASS for exact NLink.MultLe supplier and family consumer.** The internal row-disjointness and dimension-sum proof and the theta injectivity adapter are found. The deeper supplier proofs of all four hypotheses, the generic injectivity theorem body, and the detailed family error summation remain separate chunks. No new independent Lean check. A global theta-lift multiplicity growth exponent remains UNSOURCED.

## 1. Exact statement: local multiplicities have a joint rank budget

The public theorem `GlobalTheory.T.goodPointMultiplicityLeRank_proof` at [GoodPointMultiplicityLeRankProofStatement.lean:45–46](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProofStatement.lean#L45-L46) is precisely the implication

```text
for D : D7 and L : SizeData₂ D,
  SumRepresentations.Conclusion42 D
  SumRepresentations.ConclusionZ D
  Rows.IsotInternal D.what₂
  KillingConditions.LocalisationUniqueness D
  imply NLink.MultLe L.
```

The body delegates to `GlobalTheory.NLink.multLe_of_rank`. This resolves the exact type question left open in B07. The target is the local finite double-sum inequality at [BoundAtTwoThreeFamily.lean:117–119](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L117-L119). For every eligible lift j and twisted place w, the sum of good-point multiplicities over all associated local indices is bounded above by the zero-space rank at (j,w).

This theorem is a local rank-capacity bound. It is quantitative as a finite dimension inequality. It does not on its own express a global growth exponent in x, or prove a uniform analytic theta-lift multiplicity asymptotic.

## 2. Recover the proof mechanism

The implementation in [GoodPointMultiplicityLeRankProof.lean:106–149](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L106-L149) separates four steps.

### A. Local multiplicity is controlled by the selected row space

For a local index i, `goodRows D i` filters the finite row-label set to the good rows which satisfy AtM at i ([GoodPointMultiplicityLeRankProof.lean:63–65](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L63-L65)). Its associated dimension dM has an exact sum formula:

```text
dM(i) = sum_{sigma in goodRows(i)} dim_C U_(j(i),sigma)
```

where U denotes the isot row subspace. See `dM_eq_sum` at [GoodPointMultiplicityLeRankProof.lean:67–80](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L67-L80). The proof uses the internal direct-sum hypothesis to obtain indexed independence and identifies goodPartM with the finite supremum of the selected row subspaces.

The separate theorem `sum_mult_le` ([GoodPointMultiplicityLeRankProof.lean:82–100](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L82-L100)) establishes

```text
sum_{pi in Zgood(i)} mult(i,pi) <= dM(i).
```

The empty case is zero; in the nonempty case ConclusionZ supplies the exact finite sum identity, using Zgood_tie to eliminate excluded terms. We have not reopened the complete definition of ConclusionZ, so its other fields are not inferred.

### B. Labels are not counted twice

For fixed (j,w), every i in locs(j,w) shares the same j,w. At [GoodPointMultiplicityLeRankProof.lean:123–134](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L123-L134) the LocalisationUniqueness premise implies that the sets goodRows(i) are pairwise disjoint on that index set. A label appearing at two distinct local indices would violate this uniqueness condition.

Consequently the double sum of row dimensions is equal to the sum over the union of row labels ([GoodPointMultiplicityLeRankProof.lean:135–141](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L135-L141)). This is a combinatorial no-double-counting requirement, separate from linear independence of the actual subspaces.

### C. Independent subspaces supply the dimension bound

The supporting theorem `GlobalTheory.MultiplicityBound.finrank_biSup_indep` at [GoodPointMultiplicityLeRankProof.lean:50–60](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L50-L60) states that for a finite subset of an indexed independent family of subspaces of a finite-dimensional vector space over a division ring, the dimension of the finite supremum equals the sum of the dimensions. The proof uses the two-subspace dimension identity and disjointness of the new subspace from the supremum of the others.

The main theorem therefore identifies the sum over the union with the dimension of its span, and then bounds that dimension by the ambient row-space dimension ([GoodPointMultiplicityLeRankProof.lean:142–145](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L142-L145)). Pairwise intersection-zero by itself is weaker than the indexed independence needed here.

### D. The theta map preserves capacity

At [GoodPointMultiplicityLeRankProof.lean:146–149](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean#L146-L149) the ambient dimension is identified with the zero-space rank by injectivity of the theta map and the relation between the place parameter and row label.

The exact adapter `Formalism.MainNotions.J.theta_injective_of_scalars` at [NandDIVb.lean:52–57](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/AdmissibleParameterJoins/NandDIVb.lean#L52-L57) derives injectivity of thetaT from Conclusion42, IsotInternal and an eligible lift. It invokes the generic theorem `injective_of_scalars`.

The local component contract `SumRepresentations.At.Conclusion42` at [SumRepresentations.lean:177–184](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/SumRepresentations.lean#L177-L184) says, in particular, that each nonzero row subspace has a real positive scalar lam such that

```text
thetaP(thetaT(f)) = lam * f
```

for every f in that row. Its other conjuncts concern theta witnesses and base-change/cuspidality parameters. The public D-level Conclusion42 is used through h42 i sigma in the adapter. The entire D-level predicate definition and the generic injective_of_scalars implementation were not opened in this run. The actual call and local scalar condition are anchored.

The mathematical proof chain is therefore:

```text
per-index multiplicity <= selected row dimension
             |
localisation uniqueness --> disjoint row-label union
             |
indexed internal independence --> sum of row dimensions
             |
ambient row-space dimension
             |
theta map injective --> zero-space rank at (j,w).
```

The top-level supplier at [LinkNFam.lean:80–83](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean#L80-L83) (B07 receipt) uses the exact theorem, not a merely similar multiplicity predicate.

## 3. Family consumer recovered

The public wrapper `GlobalTheory.T.linkN_along_family_of_localBounds` at [LinkNAlongFamilyOfLocalBoundsStatement.lean:46–47](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBoundsStatement.lean#L46-L47) maps `ConclF Fm` to `Formalism.MainNotions.LinkN Fm`. Its implementation `GlobalTheory.LinkFam.main` at [LinkNAlongFamilyOfLocalBounds.lean:50–56](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean#L50-L56) extracts an eventual constant and family witnesses, converts each bundled Concl into an admissible table, and uses `N.linkN_of` with the family statement.

The specific conversion `admittedStatements_of_localBoundsConclusion_alt` at [AdmittedStatementsOfLocalBoundsConclusionStatement.lean:45–46](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmittedStatementsOfLocalBoundsConclusionStatement.lean#L45-L46) gives an existential table tb with `TwistedPlaces.AdmT L tb C P`, under the whole Concl L P X C. This bundle includes MultLe separately from all the other local and global conditions (B07). The wrapper delegates to `GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion`. The proof body of that conversion and its exact weighted summation are a new direct source lead, rather than an assumed consequence of this inventory.

## 4. Independent extrapolations: what can we test?

### E04-A: overlap-corrected finite capacity

Let (U_s) be a finite independent family of subspaces in an ambient finite-dimensional V, and let A_i be finite label sets. Assume nonnegative counts m_i <= sum_(s in A_i) dim U_s. Write U = union_i A_i and r_s = number of sets A_i containing s. Then

```text
sum_i m_i
 <= sum_s r_s dim U_s
 = dim(span_{s in U} U_s) + sum_{s in U} (r_s-1) dim U_s.
```

Since every s in U occurs at least once, this is valid over natural dimensions without truncated-subtraction problems. Thus

```text
sum_i m_i <= dim V + D_overlap,
D_overlap = sum_{s in U} (r_s-1) dim U_s.
```

Exact disjointness makes the defect vanish, reproducing the combinatorial and linear-algebraic part of the source proof. More generally, if the row subspaces are not independent, replace the first term by the dimension of the combined inclusion map's image plus its kernel dimension. This gives two separate measurable defects: duplicate labels and linear dependence across distinct labels. The latter is exact rank-nullity, not an additive estimate on individual ranks.

**Fixture:** three independent coordinate lines in K^3; A_1={1,2}, A_2={2,3}. At saturated local counts (2,2), the raw sum is 4, the union span dimension is 3, and the duplicate-label defect is 1. With unique labels and three distinct lines in K^2 (span of (1,0), (0,1), (1,1)), every pair intersects trivially, but the three spaces span dimension 2 rather than 3. That is a second failure mode, with relation-space dimension 1.

**Experiment:** prove the finite combinatorial weighted-count identity and joint capacity under independent subspaces, plus the two counterexamples; if direct-sum rank-nullity is included, specify the exact finite source/target spaces. Do not conflate pairwise disjoint label sets with pairwise disjoint subspaces.

### E04-B: scalar left-inverse transport and robustness

The actual injectivity adapter motivates a separate finite-dimensional result. Let V be the direct sum of finitely many U_s. Let T:V→W and P:W→V be linear. Suppose PT restricted to U_s equals lambda_s times the identity for each nonzero row, with lambda_s nonzero. Then PT is invertible, with inverse block scalars lambda_s^(-1). In particular T is injective, and rank T = dim V. This is the exact independent linear-algebra analogue of the observed scalar adapter.

For a numerical generalization, assume the direct-sum splitting is **orthogonal** in a Hilbert norm. Let A be the ideal block-scalar map, lambda_min=min_s |lambda_s|>0 over nonzero blocks. If PT=A+E and ||E||_op < lambda_min, then for every v,

```text
||PT v|| >= (lambda_min - ||E||_op) ||v||.
```

This follows from orthogonality, the block lower bound, and the reverse triangle inequality. It certifies injectivity and gives

```text
||T v|| >= ((lambda_min - ||E||_op)/||P||_op) ||v||
```

when V is nonzero and P has positive operator norm. With a nonorthogonal splitting obtained by an invertible coordinate map S, a sufficient lower bound on A is lambda_min/(||S||*||S^(-1)||). This additional condition-number cost must be accounted for; mere algebraic independence does not give an orthogonal norm estimate.

**Sharp control:** V=W=K^2, P=I, A=diag(1,1/2). Perturbation E=diag(0,-1/2) has norm 1/2 and destroys injectivity. Strict inequality matters. Another control: a zero scalar on a nonzero block defeats the exact adapter even when the remaining blocks are independently preserved.

For looped-model analysis, a learned forward/backward pair can be tested for approximate block-scalar agreement on a frozen orthogonal partition. The residual operator norm and the smallest block gain can provide a certificate of no lost directions. A finite-precision numerical result must distinguish exact rank from stable numerical rank. This is an extrapolation, not a claim about any existing model.

### E04-C: capped weighted capacity

The earlier B07 allocation inequality remains useful once a joint budget is certified. For nonnegative masses m_i<=u_i and sum m_i<=R, every lambda>=0 certifies sum m_i e_i<=lambda R+sum u_i max(e_i-lambda,0). The proof of MultLe now supplies the actual form of a joint rank budget, but the upstream weighted aggregate and coefficients still need to be inspected. An independent weighted dual certificate may be checked before connecting it to the arithmetic proof.

## 5. Next work and acceptance

The exact registered MultLe supplier and family consumer are FOUND. The independent paper consequences above are ready for a separate Lean experiment. Recommended next **RH-26E-04A**: finite label multiplicity accounting, independent-subspace rank budget, overlap defects and falsifying fixtures. A subsequent E04B can formalize block-scalar injectivity and the perturbation threshold. The source-only **RH-26B-09** queue should inspect the implementation `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmittedStatementsOfLocalBoundsConclusion.lean` and the generic scalar injection dependency `src/Formalism/SharpRestriction/AdmissibleParameterJoins/NandDIVa.lean` in separately registered bounded chunks; the latter is a direct import of NandDIVb, not a verified declaration location. Preserve both lines of work in the rolling inventory.

## 6. Source receipt

Seven distinct upstream Lean files, **657 returned source lines**, at the frozen pin:

| Path relative to src/ | Read window |
| --- | --- |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProofStatement.lean` | 1–46 (46) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBoundsStatement.lean` | 1–47 (47) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProof.lean` | 1–149 (149) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean` | 1–58 (58) |
| `Formalism/SharpRestriction/LevelLetterCocycles/SumRepresentations.lean` | 1–250 (250, cap) |
| `Formalism/SharpRestriction/AdmissibleParameterJoins/NandDIVb.lean` | 1–61 (61) |
| `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmittedStatementsOfLocalBoundsConclusionStatement.lean` | 1–46 (46) |

No full-repository scan or build, upstream code imported, independent Lean run, GPU/QPU, or paid compute. Runtime/RAM unmeasured. Earlier source anchors reused from pinned B07 without rereading. The full proof of the deeper generic injection and admissible-table conversion lies outside this read boundary.

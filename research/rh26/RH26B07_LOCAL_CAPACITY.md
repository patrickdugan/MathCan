# RH-26B-07 — local multiplicity, rank capacity, and transfer certificates

**Date:** 2026-11-24. **Registration:** [RH26B07_REGISTRATION.md](RH26B07_REGISTRATION.md), commit `88f0a66a5056e87892c30a409fe46ef680f22e92` before new upstream source reads.  
**Frozen source:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`; observed consolidated main `f38c099ec6017a3ce839cba4e06857eda6c9a057`. No equivalence claim.  
**Disposition:** **PASS for chunk inventory and exact bundled role**; **PARTIAL for the exact multiplicity supplier**. Found a direct call to `goodPointMultiplicityLeRank_proof` on the linked-family route and its explicit import, along with a separate rank/containment theorem involving theta spans. Their exact target-type equivalence to `MultLe` is not established in this window. Quantitative global theta-lift growth exponent remains UNSOURCED. The new independent mathematics below is paper algebra and proposed tests, not a kernel-verified upstream theorem.

## 1. Local capacity inequality

`GlobalTheory.NLink.MultLe` at [BoundAtTwoThreeFamily.lean:117–119](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L117-L119) is a proposition for a given `L : SizeData₂ D`. For each lift j in the specified finite lift set and each twisted place w, it requires

```text
sum_{i in D.nd.locs j w} sum_{pi in D.nd.Zgood i} D.nd.mult i pi
    <= L.zeroSpaceRankAtPlace j w
```

with real casts of the multiplicities and rank. The key structure is a *joint budget* over the pair index (i,pi), for every eligible (j,w). A bound on each individual summand would not suffice.

`Concl L P X C` ([BoundAtTwoThreeFamily.lean:154–169](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L154-L169)) requires this field separately from `rank : TwistedPlaces.adm3 L`, the pointwise `Bd` inequalities, killing, numeric row assumptions, local exceptional sets and other constraints. `ConclF` ([BoundAtTwoThreeFamily.lean:171–173](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L171-L173)) requires an eventual family witness X and the entire Concl under `ShaFinOdd`. The resulting local capacity budget is therefore not the whole local bound or a stand-alone global theta estimate.

The nearby `Bd` at lines 52–54 bounds a local valuation-like quantity vcc by sPi, an error b, and place corrections. The separate capacity bound and local coefficient estimates suggest a useful weighted aggregation interface, conditional on nonnegative multiplicities and appropriate uniform local bounds. No source identity expressing the full aggregate as that weighted sum was read in this session.

## 2. Exact next supplier and linked-family consumer

`UpperTheory.GalC.linkN_of_twGood_galoisPreconditions` at [LinkNFam.lean:65–83](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean#L65-L83) starts from `Hypotheses₂`, a cut supplier, `TwGood Fm`, and eventual Galois preconditions and Tie4 for every family index. It constructs a good cut at each eligible index, builds `FactsFAlt` for the cut family, and invokes `conclF_of_family_facts_and_bound_at_two_three`, followed by `linkN_along_family_of_localBounds` and `linkN_of_gd`.

Crucially, the remaining obligation in that application is discharged by **`GlobalTheory.T.goodPointMultiplicityLeRank_proof`** at [LinkNFam.lean:80–83](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean#L80-L83). Its arguments are fields of the original Galois precondition object. The declaration's explicit imported source is

`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProofStatement.lean` (LinkNFam.lean line 12).

The neighboring import `LinkNAlongFamilyOfLocalBoundsStatement.lean` (line 13) is the next named bridge from the local bounds. This is a precise proof-supplier lead; we have not yet read the supplier type or checked that it concludes exactly NLink.MultLe rather than another good-point rank predicate. Do not identify the two until the actual signature and coercion path are inspected.

The family result is used by the slot-norm and linked-family adapters at [LinkNFam.lean:84–116](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean#L84-L116). Those are the connections to the higher argument; they preserve the row conditions and require the two/three-place bound as a separate input.

## 3. Distinguish adjacent multiplicity and rank chunks

Three independently meaningful structures surfaced.

**Level-transfer composition.** The theorem `GlobalTheory.HeightCounting.Up.multiplicity_bound_of_local_components_alt` at [MultiplicityBoundOfLocalComponents.lean:50–57](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MultiplicityBoundOfLocalComponents.lean#L50-L57) supplies `MoveToBase hL` from published third-layer inputs and SerN. Its proof chains a level-I-to-B1 transfer and an existence theorem for a carried B2 level, composing preservation relations on the intermediate witnesses. This theorem has a transfer contract, not the displayed sum inequality. Its import `MultiplicityBoundTransferOfCmDatum.lean` is a future source lead. A useful independent theorem would formalize composition of certificate-preserving maps with a resource budget; it needs the actual MoveToBase definition before any claim of fidelity.

**Local theta span and lattice containment.** The theorem `GlobalTheory.BigOn.rank_at_twisted_places_of_rec_span` at [RankAtPlacesRec.lean:76–85](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RankAtPlacesRec.lean#L76-L85) concludes `GlobalTheory.TraceClassRank.RankAtPlaces O` from point conditions, recurrence witnesses, span-over-classes, leaf span/data, and a comparison off an own-place subset. At [RankAtPlacesRec.lean:93–113](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RankAtPlacesRec.lean#L93-L113) it obtains a leaf projection, forms-determined condition, commuting endomorphism, finite generation of each theta lattice, containment in a restricted eigenspace, and localized containment of the initial lattice in the comparison theta lattice. It then invokes `eigenlattice_local_containment_at_pairs` for a place and its conjugate. The family lift at [RankAtPlacesRec.lean:116–127](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RankAtPlacesRec.lean#L116-L127) retains separate maximality, geometric and comparison inputs. This is a source-anchored theta-to-rank route, whose relation to the local multiplicity inequality remains an open dependency. Direct imports `RankAtPlacesFromComparison.lean`, `EigenlatticeLocalContainmentAtPairsStatement.lean`, and `TraceLatticeLeThetaLatticeAtPlace.lean` identify future chunks.

**Coefficient localization.** `localMultiplicityFamily` at [LocalMultiplicityFamily.lean:98–107](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LocalMultiplicityFamily.lean#L98-L107) transports an existing MtFam record into localized data. The same file transports a theta tie ([LocalMultiplicityFamily.lean:115–127](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LocalMultiplicityFamily.lean#L115-L127)) and kept character choice (129–132). This is a data-transport interface, not a new sum-of-multiplicities inequality.

The other reads identify independent future blocks: `ConclOfGrp` has a separate HeightCounting.TopA.ConclAlt based on automorphic/Galois and local-type realizability ([ConclOfGrp.lean:60–85](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ConclOfGrp.lean#L60-L85)); `conclusion42_of_parts` builds a reduced parameter witness from a theta lift/base-change parameter and disjointness of types ([Conclusion42OfParts.lean:51–62](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Conclusion42OfParts.lean#L51-L62)); `conclusion_split_alt` uses local Tate/Bloch–Kato, jump and crystalline information in a local Sha-bound argument ([ConclusionSplitOfHub.lean:71–82](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ConclusionSplitOfHub.lean#L71-L82), [ConclusionSplitOfHub.lean:119–132](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ConclusionSplitOfHub.lean#L119-L132)). Their names must not be conflated with NLink.Concl.

## 4. Independent mathematical extensions to try

### E04-A: certify a joint capacity by independent subspaces

Let K be a field, Z finite-dimensional, I a finite index set, and V_i finite-dimensional. Write m_i=dim V_i and let f_i:V_i→Z be linear. Form the common map F: direct sum_i V_i→Z by summing the f_i.

Rank-nullity gives the *exact redundancy identity*

```text
sum_i m_i = rank(F) + dim ker(F).
```

If F is injective, sum_i m_i≤dim Z. Equivalently, for individually injective f_i, independence of their images is sufficient. Individually injective maps alone are insufficient: two one-dimensional maps into the same one-dimensional space satisfy both individual rank bounds, while the joint budget 2≤1 fails. Their combined map has a one-dimensional kernel. This defect identity isolates the missing overlap certificate.

**Proposed Lean gate:** prove the rank-nullity identity for a finite product/direct sum and derive the joint capacity for an injective combined map; verify a two-map overlap counterexample. Use independent fresh definitions and Mathlib 4.35. Do not treat this toy as the actual proof of MultLe until the upstream rank supplier is inspected. A later numerical companion can test exact-rank and near-dependent matrices, but numerical SVD alone cannot certify exact rank without an error bound.

### E04-B: weighted capacity and sharp dual upper bound

Assume finite nonnegative real multiplicities m_i, upper capacities u_i, a total budget sum_i m_i≤R, and real coefficients e_i. For every lambda≥0,

```text
sum_i m_i e_i
 <= lambda R + sum_i u_i max(e_i-lambda,0).
```

Proof: split e_i into lambda+(e_i-lambda); multiply by m_i≥0, bound the positive excess by u_i max(e_i-lambda,0), and use lambda≥0 on the budget. This is an elementary dual certificate for a capped allocation. Without the upper capacities, the safe bound for nonnegative e_i is R*max_i e_i.

There is an exact greedy solution for nonnegative coefficients: sort in descending order, allocate up to each u_i until the budget is exhausted. A threshold lambda equal to the boundary coefficient (or zero when all positive capacities fit) makes the dual bound tight. This holds for integer capacities and integer total budget as well, since the allocation can be taken integral. Ties are harmless but certificate values can be nonunique.

A diagnostic fixture: e=(9,5,1), u=(2,3,4), R=4. The allocation (2,2,0) scores 28. At lambda=5, the certificate gives 5*4+2*(9-5)=28; the crude maximum bound gives 36. A control using negative weights or missing caps must test the appropriate premise, rather than silently treating every component as saturated.

**Proposed Lean gate:** prove the dual inequality for arbitrary finite index set; verify the exact fixture; demonstrate why omitting an upper cap or nonnegative multiplier/budget premise breaks the claimed bound. A separate greedy-optimality proof may be added after this smaller certificate passes.

### Possible extension: local-to-global log-weighted allocation

If a later source inspection establishes actual nonnegative local weighted aggregation and budgets R_(j,w), the same inequality can be applied at each eligible (j,w) and summed with nonnegative place weights, e.g. log p for p>1. Repeated component indices across places require either a disjoint sum domain or an explicit overlap multiplicity accounting. This is conditional speculation; the source has not yet licensed global optimization or a quantitative theta exponent.

## 5. Bounded read receipt and next experiment

Eight frozen files, **976 returned source lines**, with the first-window limits recorded below.

| Source path relative to src/ | Window |
| --- | --- |
| `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean` | 1–177 (177) |
| `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MultiplicityBoundOfLocalComponents.lean` | 1–67 (67) |
| `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ConclOfGrp.lean` | 1–150 (150) |
| `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RankAtPlacesRec.lean` | 1–129 (129) |
| `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LocalMultiplicityFamily.lean` | 1–135 (135) |
| `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Conclusion42OfParts.lean` | 1–64 (64) |
| `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ConclusionSplitOfHub.lean` | 1–135 (135) |
| `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean` | 1–119 (119) |

Only targeted directory filename metadata was queried beyond the source windows. No full upstream scan, clone/build, new kernel run, GPU/QPU or paid compute. Runtime and RAM unmeasured.

**Next B08:** preregister a fresh bounded read of the explicit supplier `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodPointMultiplicityLeRankProofStatement.lean` and the accompanying `LinkNAlongFamilyOfLocalBoundsStatement.lean`. Recover the exact good-point rank predicate, its hypotheses, and any explicit conversion to NLink.MultLe. Follow the closest imported implementation or local rank definition; preserve distinctions until confirmed. Then choose E04-A or E04-B as a separate registered kernel run. Continue updating [CHUNK_INVENTORY.md](CHUNK_INVENTORY.md).

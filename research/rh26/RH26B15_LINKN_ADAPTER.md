# RH26B15: LinkN family adapter and analytic boundary

Date 2026-11-24 Asia/Manila. Registration 5b24c5204ea2d5ff954abe2a1175b80d1988a298. Frozen upstream c900e67c2fcd1fdb041685820bbd2b867fbc5a4b. **SOURCE PASS for N.linkN_of and exact LinkN contract.** Analytic conversion to DIVinN remains open; no upstream kernel execution or arithmetic modification.

## Exact coefficient and quantifiers

[ExportFamilies.lean:49–66](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/StatementFamilies/ExportFamilies.lean#L49-L66) defines OrbitValuationBound as existence of one C,x0 for all x>=x0 and all i in Fm.Ix x, with aux₃ (Fm.L x i) C. AdmFC has its additional Fm.x1<x parameter proof; AdmF existentially quantifies the input constant. UniformExportStatement chooses output C from input Ca before quantifying over Fm. stmtF_of_stmtU preserves C and the family threshold x0.

[ThetaScalarFamilyOfEigenvalue.lean:49–57](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/LevelLetterCocycles/ThetaScalarFamilyOfEigenvalue.lean#L49-L57) contains the actual two adapter proofs:
- export_link_of_family unpacks the same C,x0 and applies the family result at x,i; unfolds aux₃ and supplies hsha, hS, j, hj.
- linkN_of Fm hA hS is export_link_of_family Fm (hS hA).

No extra scale factor, threshold increase, coefficient sign condition, or new arithmetic estimate occurs in these bodies. The original 2000*(|Ca|+1)^3 output would be transported unchanged if a source-compatible replacement were established; the same holds for 1002 or 105. The existing upstream statement is existential and gives no numeric witness until the supplier is inspected (B14).

[GlobalTheoremInputs.lean:52–71](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L52-L71) explicitly defines ShaFinOdd, vvTerm, etaSum, LinkN_at and LinkN. LinkN has one C,x0, then all x>=x0,i, the ShaFinOdd premise, all eligible j, and LinkN_at has the summability implication. Thus, writing g=L.sc.L, R=dZ0(j), X=f*m*b*g², N=(log x)²*Nc and V=tsum vvTerm, its pointwise conclusion is exactly etaSum <= R*(C*(X+N)+V). Preserve both cohomological assumptions.

## Next conversion boundary

[GlobalTheoremInputs.lean:76–87](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L76-L87) defines SmallLevelRankEq, requiring eventually dZ0(j)=D0 for every eligible j, and DIVinN_at, which asks instead for etaSum <= D0*C*x^eps*(B0+Nc). DIVinN asserts this uniformly with an existential C,x0 and has no explicit ShaFinOdd or Summable premises. Those must be obtained by the actual conversion or another supplier. The coefficient replacement at LinkN alone cannot supply them.

[GlobalTheoremInputs.lean:101–119](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L101-L119) defines the multi-conjunct LinkDIV_at contract and LinkDIVt as LinkEta -> DIVinN -> LinkDIV. At 182–188 the GlobalTheoremInputs tuple is LinkG, LinkS, LinkIRR, LinkDIV, LinkMu; LinkGLOBAL additionally requires ChosenE and yields eventual ChainTied on Fm.Win. These are exact declaration boundaries, not yet their supplying proofs.

## Independent scalar test proposal E06A

Put W=x^eps*(B0+Nc). Under R=D0>=0, K>=0, X+N<=a*W and V<=v*W, the LinkN envelope yields etaSum<=D0*(K*a+v)*W by monotone multiplication and addition. The same hypotheses permit separate X<=aX*W and N<=aN*W with a=aX+aN. Any W=0 case requires the numerator bounds themselves, not a quotient. If the constants and thresholds are uniform on the family, their maximum threshold and coefficient K*a+v suffice. This is a conditional scalar deduction, not a recovered DIVinN proof. Keep the distinction between the numerical factor multiplying X+N and the additive cohomology coefficient; only the former changes from 2000 to 105.

Control: D0=R=1,W=1,X+N=1,V=1000,K=1 violates the putative coefficient-1 conversion, while satisfying the LinkN bound at etaSum=1001. A missing rank equality can also break conversion (R=2,D0=1,W=1,X+N=1,V=0,K=1,etaSum=2). For uniformity, arbitrary dependence of v on x cannot be replaced by a fixed coefficient without a bound.

## Nearby theta lemma

ThetaScalarFamilyOfEigenvalue.lean:59–90 defines ThetaScalarNonzero and LamPos and proves thetaT_injective (63–85). Given an internal direct sum of isot spaces, all thetas' composite eigenvalues are nonzero on their respective components; the span is contained in the supremum of nonzero eigenspaces, independent from the zero eigenspace, so the composite kernel is trivial. This proves injectivity under the stated assumptions. It gives no quantitative uniform eigenvalue lower bound or global multiplicity exponent by itself.

## Read receipt

Four distinct source files: GlobalTheoremInputs.lean (192 lines), ThetaScalarFamilyOfEigenvalue.lean (94), ExportFamilies.lean (90), DataParamsS.lean (52; thin wrapper defining hsSq). 428 distinct returned lines, 714 counting repeated anchor extraction. No new proof execution, upstream build, or paid compute.

Next B16: preregister targeted declaration discovery for the actual LinkN -> DIVinN theorem(s); follow rank equality, cohomology finiteness/summability, B0/Nc scale absorption and family threshold. Then locate LinkDIVt application and actual analytic consumer; no global exponent conclusion yet.

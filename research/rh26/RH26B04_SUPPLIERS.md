# RH-26B-04: exact bundled supplier of theta transport premises

**Registered:** [RH26B04_REGISTRATION.md](RH26B04_REGISTRATION.md), committed before new upstream source reads.  
**Date:** 2026-11-23.  
**Pinned upstream commit:** `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b` (the same fixed commit used by RH-26B-01 through RH-26B-03).  
**Observed upstream main at session start:** `97ed34c57bc0d159b51c77a9e7e2ba59932b1256` (**changed** from the pinned commit). No silent ref update. Current-main deltas and their possible effect on this subtheory were not audited.  
**MathCan:** branch `research/rh26-extraction-rubrics-20261123`, draft [PR #265](https://github.com/patrickdugan/MathCan/pull/265).  
**Disposition:** **PASS** for one precise upstream supplier of the *entire* `ThetaIntegralsAgree ∧ LocalMatching` conjunction; **PARTIAL** on the internal standalone supplies of `StepAlpha`, `StepBeta`, and `OneConst`; quantitative multiplicity and `X/m+m` error remain **UNSOURCED**. This is an upstream static source trace, not a new Lean kernel verification.

## 1. Source-backed conditional cut

The literal upstream theorem at [EveryCharacterOfLiteratureOfVWin.lean:570–571](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L570-L571) is:

```lean
theorem UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature
    (O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree ∧
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching :=
  PositivityTheory.ThKR.theoremK_head2
    (UpperTheory.LiteratureTheorems.eis_bl_of_literature O)
    (UpperTheory.LiteratureTheorems.siegel_weil_std_of_literature O)
```

(The code block is a short transcribed interface for orientation; consult the linked original for exact qualification.)

The decisive bundled supplier is `PositivityTheory.ThKR.theoremK_head2`, declared at [TheoremKOfMod.lean:72–73](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean#L72-L73). It has **exactly two mathematical inputs** on that public interface:

- `GlobalTheory.ThK.Dbl.EisBL`, supplied in the top-level literature by `eis_bl_of_literature O`;
- `GlobalTheory.ThK.Dbl.SiegelWeilStd`, supplied by `siegel_weil_std_of_literature O`.

Its conclusion is the entire `WeilTensorModels.ThetaIntegralsAgree ∧ WeilTensorModels.LocalMatching`. The helper `theoremK_head2_of_mod` at [TheoremKOfMod.lean:64–70](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean#L64-L70) additionally takes `PositivityTheory.Sph.ModSt`; the public theorem discharges this using `PositivityTheory.Sph.modSt2`.

This is a **precise theorem-supplier anchor**. It is still conditional on the two substantial analytic inputs; the path from their own proof sources was not read in this session.

## 2. Construction chain downstream of the supplier

Within `theoremK_head2_of_mod`, the conclusion comes from `PositivityTheory.Sph.Tr.closeSph`, supplied with ramified and inert local data, spherical matching, infinitesimal Lie data, Siegel-set data, the two analytic hypotheses, and Weil-representation existence. See [TheoremKOfMod.lean:64–70](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean#L64-L70).

The declaration `PositivityTheory.Sph.Tr.closeSph` is defined at [CloseSph.lean:157–172](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/CloseSph.lean#L157-L172). Its body assembles an extensive record of intermediate interfaces, including:

- `KCoinv` from a dictionary and an input hypothesis [CloseSph.lean:179–183](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/CloseSph.lean#L179-L183).
- `EndA` and `EndB` from the paired theorem `PositivityTheory.Sph.Tr.endAB_sph`, with the **same Siegel–Weil and Eisenstein inputs**, at [CloseSph.lean:317–320](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/CloseSph.lean#L317-L320).
- A consolidated `PositivityTheory.ThKG.Leaves` record, followed by the final application of `PositivityTheory.ThKG.agree_of_leaves`, at [CloseSph.lean:321–322](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/CloseSph.lean#L321-L322).

The standalone declaration `endAB_sph` at [EndCore.lean:172–183](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/EndCore.lean#L172-L183) explicitly concludes `GlobalTheory.ThK.EndA ∧ GlobalTheory.ThK.EndB` under two analytic hypotheses and several geometric, finite-place, and Lie-theoretic inputs. This establishes a **rank/endgame intermediate interface**. Its exact fields and relationship to `StepAlpha`, `StepBeta`, and `OneConst` were not opened and are **not inferred from the names**.

The resulting source-level graph is:

```text
O : OpenLiteratureStatements
    ├─► eis_bl_of_literature O : ThK.Dbl.EisBL
    └─► siegel_weil_std_of_literature O : ThK.Dbl.SiegelWeilStd
                  │                       │
                  └──────────┬────────────┘
                             ▼
       ThKR.theoremK_head2_of_mod(Sph.ModSt)
                             │
                             ▼
                        Sph.Tr.closeSph
                     ┌───────┴────────┐
                     ▼                ▼
              Sph.Tr.endAB_sph    local, coinvariant,
                → EndA ∧ EndB      spherical and decay inputs
                     └───────┬────────┘
                             ▼
                ThKG.Leaves + KDecay + KCoinv
                             │
                             ▼
                   ThKG.agree_of_leaves
                             │
                             ▼
        WeilTensorModels.ThetaIntegralsAgree ∧ LocalMatching
                             │
                             ▼
      original Decay / OneConst / Coinv and StepBeta / StepAlpha
```

The bottom implications follow by unfolding the original **conjunction** `ThetaIntegralsAgree` at [WeilTensorModels.lean:623–630](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L623-L630), inspected and source-anchored in [RH26B03_ORIGINAL_PREMISES.md](RH26B03_ORIGINAL_PREMISES.md).

### Per-target disposition

| Target | Status | Exact evidence | Remaining proof gap |
| --- | --- | --- | --- |
| Full `ThetaIntegralsAgree ∧ LocalMatching` | **FOUND** | `theoremK_head2` and `theoremK_head2_of_mod`, [TheoremKOfMod.lean:64–73](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean#L64-L73) | Its internal hypotheses are substantial, but exact supplier type is proved in pinned source |
| `OneConst` | **FOUND through bundled implication / INTERNAL PARTIAL** | From the first conjunct of `ThetaIntegralsAgree` and its universal `IsMatched → OneConst ∧ Coinv` statement, [WeilTensorModels.lean:623–630](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L623-L630) | Identify how `agree_of_leaves` constructs `OneConst` |
| `StepBeta` | **FOUND through bundled implication / INTERNAL PARTIAL** | `ThetaIntegralsAgree` second conjunct supplies existential beta-unit parameters, [WeilTensorModels.lean:627–629](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L627-L629) | Trace to `EndB` or other actual proof; inspect signatures before assuming path |
| `StepAlpha` | **FOUND through bundled implication / INTERNAL PARTIAL** | `ThetaIntegralsAgree` third conjunct supplies existential alpha-unit parameters, [WeilTensorModels.lean:629–630](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L629-L630) | Trace to `EndA` or other actual proof; inspect signatures before assuming path |

The first conjunct requires `Decay` and then `OneConst` / `Coinv` for every matched pair. The beta and alpha existential integer-unit triples remain **separate**; the present source supplies them via the full conjunction, not a shared witness.

## 3. Auxiliary files checked and excluded from the claimed supplier

The following source windows provide small local machinery but **do not themselves prove `WeilTensorModels.ThetaIntegralsAgree`**:

- [ThetaIntegralsOfMinguez.lean:63–68](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ThetaIntegralsOfMinguez.lean#L63-L68): `GlobalTheory.SquareAgree.I_smul` proves scalar linearity of a theta integral, useful for scalar comparison normalization.
- [MatchedThetaIntegralValue.lean:94–136](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatchedThetaIntegralValue.lean#L94-L136): invariance of integrals under translation and a finite-sum integration identity.
- [StepUnfold.lean:159–165](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Statements/HeckeThetaIntegrals/StepUnfold.lean#L159-L165): `StepProj`, `StepFlip`, `StepUnfold`, and `StepJets` are **different** grid/row propositions with different types and must not be conflated with `StepAlpha` / `StepBeta`.
- [FormulaAtOfSteps.lean:58–81](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Statements/HeckeThetaIntegrals/FormulaAtOfSteps.lean#L58-L81): `exists_isTermVol` constructs a measure/fundamental-domain witness for those grid steps, not the global two-rank theta transport theorem.

These checks prevent a common failure mode: a matching word in a filename or Lean declaration is insufficient to identify the exact supplier.

## 4. Mathematical interpretation and falsifiers

The promising compression boundary is the **conditional bridge from Eisenstein continuation and Siegel–Weil to theta-integral comparison and matching**, with the internal endgame and coinvariant hypotheses explicit.

Any replacement must account for:
- the source-level `EisBL` and `SiegelWeilStd` inputs, including their actual quantitative domains and normalizations;
- archimedean Lie compatibility, local ramified/inert matching, and spherical quotient conditions assembled in `closeSph`;
- a constructed `OneConst` nonzero scalar plus the independent alpha/beta step identities from the original `ThetaIntegralsAgree` predicate.

**Registered null upheld as plausible:** this is a substantial proof bundle. The extracted two-input theorem is a strong interface for researching compression, but its output cannot be reproduced by a mere identity of functions or toy scalar map. The six Lean lemmas from RH-26E-01 independently certify only field algebra once the nonzero scalars and rank-step equations are assumed.

No proof of a quantitative theta-lift multiplicity exponent or of `E(X,m) ≍ X/m+m` was located in this bounded read. Keep RH-26C and the quantitative RH-26B hypothesis **UNSOURCED**.

## 5. Exact next session

**RH-26B-05:** preregister a new source-only check, then inspect:
1. `src/Development/WeilBound/ThetaLifts/AgreeOfLeaves.lean` to recover the exact `agree_of_leaves` theorem and how `OneConst`, `StepAlpha`, `StepBeta` are discharged;
2. `src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/EndCore.lean` **after line 210**, to locate the `EndA`/`EndB` construction and any explicit rank-step proof supplier;
3. if still within budget, `src/Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesS.lean` for the `EisBL` and `SiegelWeilStd` input statements.

Check the precise theorem signatures and hypothesis flow. Source-only file/line receipts and unchanged pinned SHA required. Prove any proposed operator reduction independently in a *separate* MathCan Lean module and CPU workflow only after the exact mathematical claims are identified.

## 6. Bounded read receipt

Eight distinct upstream Lean files, **approximately 1,195 source-line responses/requests including counted one-line probes**. All use pinned upstream `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`.

| File | Read ranges | Count |
| --- | --- | ---: |
| `Development/AbelianVarietyTheory/Statements/HeckeThetaIntegrals/StepUnfold.lean` | 1–169 | 169 |
| `Development/AbelianVarietyTheory/Statements/HeckeThetaIntegrals/FormulaAtOfSteps.lean` | 1–85 | 85 |
| `Development/AbelianVarietyTheory/Proofs/TwistedOperators/ThetaIntegralsOfMinguez.lean` | 1–72 | 72 |
| `Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatchedThetaIntegralValue.lean` | 1–157 | 157 |
| `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean` | 470–655 | 186 |
| `Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean` | 1–75 | 75 |
| `Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/CloseSph.lean` | 1–210, one-line probes 250/300/350/400/450/500/550, 299–322 | 241, conservatively |
| `Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/EndCore.lean` | 1–210 | 210 |

Total **1,195** under the 1,200-line budget. Source windows in `CloseSph` overlap by one line (300); a few probes beyond its EOF returned blank content. Those are conservatively counted, so the stated total does not underreport requests.

Read-only GitHub API metadata searches were limited to selected directory trees (including the 780-file `WeilBound/ThetaLifts` filename index); **no repository-wide source scan, full clone, upstream build or Lean kernel recheck**. No GPU/QPU/paid compute. Published external guide pages were consulted as navigation clues; exact mathematical findings in this report are anchored to the pinned upstream Lean files above.

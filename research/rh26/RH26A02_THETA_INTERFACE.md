# RH-26A-02 — seven-input theta / window cut

**Date:** 2026-11-23  
**Upstream commit:** `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`  
**Disposition:** **PASS (static interface-discovery rubric)**, **BLOCKED (RH-26B quantitative theta-multiplicity extraction)**. This study is a source reading, not an independent Lean kernel check.  
**Research branch:** `research/rh26-extraction-rubrics-20261123`, MathCan PR #265.

## 1. Precise theorem under the boundary

The decisive theorem is `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` in [SiegelEisensteinSecondTermHypotheses.lean:101-105](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L101-L105). Its interface is:

| Input | Exact Lean type | Function in this proof |
| --- | --- | --- |
| `P` | `GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses` | Supplies Green regular-character input and the unitary/automorphic hypotheses consumed by the witness constructor |
| `F` | `GlobalTheory.FunPr.ThetaLocalInputs` | Provides local theta data, test-vector and representation inputs |
| `hA` | `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree` | Used in witness/test-vector and evaluation-grid construction |
| `hM` | `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching` | Used alongside `hA` in the same construction |
| `hX` | `GlobalTheory.CovTop.CovolumeBoundOfX` | Fed into linked-bundle construction |
| `hL` | `UpperTheory.Zero.LLC.RecTExists` | Supplies local-parameter dependence and linked-bound interface |
| `hV` | `UpperTheory.Top.VWin` | Supplies windowed cohomology bounds to the zero-freeness criterion |

Output: `UpperTheory.EveryCharacter`, the universal half-plane nonvanishing proposition for Dirichlet L-functions.

**The cut is a proof of a conditional implication at the interface.** The surrounding upstream library supplies the inputs to get the unconditional top-level theorem. It is not a standalone elementary proof of RH or GRH.

## 2. The intermediate witness construction

The theorem above uses `GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters` and produces a witness of `Nonempty (GlobalTheory.Fc.HypsAlt S0.NL GlobalTheory.Fc.DefiniteSideCondition)` through `nonempty_hyps_definite_side_of_closed_bound` ([SiegelEisensteinSecondTermHypotheses.lean:76-105](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L76-L105)).

The witness constructor has the schematic data flow:

```text
F + P + hA + hM
    ├── functionalsSeparate (Howe / Siegel-Weil inputs)
    ├── rational/test-vector row
    ├── Fourier-coefficient fit
    └── evaluation-grid witness CF1
P + Fourier fit ──► row function witness CF0
hL + parameters at max(CF0, CF1) ──► open parameter + extension
hX + P + hL + extension ──► linked-bundle witness
linked bound hN + all witnesses ──► Nonempty HypsAlt

Green(P) + hV + Nonempty HypsAlt
    └── every_character_of_green_v_win
          └── primitive zero-free criterion (window width 3/2)
                └── imprimitive extension
                      └── EveryCharacter
```

This diagram follows [SiegelEisensteinSecondTermHypotheses.lean:77-105](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L77-L105) and [TopPlug.lean:50-56](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean#L50-L56). The `max(CF0,CF1)` synchronization is concrete: the final witness uses one shared grid scale, which is an important constraint for future attempts to simplify its construction.

The `HypsAlt` target is a long dependent structure, not an unspecified black-box Boolean: its recorded fields include a family class, raw selection, row/period/volume conditions and the target `nRest : N (D3 3 𝒜)`. The structure's precise type is at [Hyps.lean:54-122](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean#L54-L122). Those hypotheses cannot be dropped from a proposed operator-theoretic abstraction.

The linked-bound input `hN` is produced by `UpperTheory.N.boundAtTwoThree_linked_of_recT` from `Hypotheses₂`, as shown at [At23OfAll.lean:49-57](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/At23OfAll.lean#L49-L57). The actual numerical content of `BoundAtTwoThreeFamilyFonAlt` remains uninspected.

## 3. Exact `OpenLiteratureStatements` interface

`UpperTheory.LiteratureTheorems.OpenLiteratureStatements` is a three-field `Prop` structure ([EveryCharacterOfLiteratureOfVWin.lean:220-223](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L220-L223)):

```text
caraianiLocalGlobalDual : UpperTheory.One.M.Row
localLanglandsExists     : UpperTheory.Zero.LLC.RecTExists
galoisRepOfPolarizedPairLit : UpperTheory.One.M.Row
```

The same Galois row is supplied to two separate fields at the upstream `everyCharacter_of_row` call. This is an interface observation; it neither determines the semantic adequacy of those row statements nor identifies all downstream use sites.

## 4. Exact `VWin` statement and role

`VWin := ∀ ψ : PChar, VWinAt ψ 401` at [ExistsPageN.lean:84-92](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L84-L92). For each primitive character `ψ`, `VWinAt` quantifies over `0 < ε < 1/52`, a function `e(x)` satisfying a base-2 scale condition `PageN`, and sufficiently large `X`. Under the arithmetic prime-pair condition `WinPair`, it supplies a `Y` with `X^(1/J) ≤ Y` and `Y² ≤ X`, such that every `x ∈ [Y,Y²]` satisfies `VAt ψ ε 401 q d (e x) x`.

Here `VAt` asks for a `VVle` bound for number fields `E` satisfying `IsChiField` ([ExistsPageN.lean:55-90](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L55-L90)). `VVle E t B` requires finiteness of designated Tate–Shafarevich lengths below `t` and bounds the weighted sum of those lengths over arbitrary finite sets of primes by `B`; for `VAt`, `t = ⌊x^401⌋₊` and `B = sqrt(exp(x^ε))`. The precise quantifiers over closures and Galois-cohomology input data appear in the definition.

The consumer at [TopPlug.lean:50-56](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean#L50-L56) fixes `la = 3/2`, applies `UpperTheory.Top.supplyChi ψ (hV ψ)`, and obtains `ZeroFreeAll`; `UpperTheory.Top.imprimitive` extends to all characters. The supplier declaration is at [SupplyChi.lean:46-54](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean#L46-L54), and the terminal analytic criterion `zeroFreeAll_of_topG` at [ZeroFreeAllOfTopG.lean:66-74](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean#L66-L74). This identifies exactly **where the cohomological window enters the analytic zero-free chain**.

## 5. What this establishes and what it leaves open

**Established by source inspection:** the named seven-premise interface, explicit use of theta-integral agreement and local matching in the witness constructor, the shared grid-scale gate, the cohomological `VWin` statement with exponent 401, the linked bound from primes 2 and 3 at the level of predicates, and the `la=3/2` analytic bridge.

**Unresolved mathematics:** (a) exact definitions and normalization of the theta integral and local matching operations; (b) geometric or representation-theoretic source of the `ThetaIntegralsAgree`/`LocalMatching` proofs; (c) exact numeric inequalities inside `BoundAtTwoThreeFamilyFonAlt`; (d) a quantitative theta-lift multiplicity lemma; (e) a faithful derivation of `X/m+m` prime-sum error; (f) independent Lean proof checks.

**Null/obstruction:** a simplified theta operator that proves an isolated equality of integrals may still fail to provide a nonempty `HypsAlt` witness with compatible grid, volume, linking, and window data. That is the immediate falsifier for a compression claim.

## 6. Exact next-session plan (RH-26B discovery gate)

From this document and `LEDGER.md` only, start a new capped run (8 files / 1,200 lines / two hops). First inspect the signatures and source of `ThetaIntegralsAgree` and `LocalMatching`, using these known imported files as entry points:

- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSquareThetaIntegralsEq.lean`
- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSquareLocalMatching.lean`
- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BoundAtTwoThreeFamilyFon.lean`

Trace only the definitions of the relevant operators and the first quantitative inequality with a checked source anchor. Disposition is UNSOURCED if these cannot be found within budget. The independent finite-dimensional analogy should wait until those types are known.

## Read budget receipt

Eight distinct upstream files, **708 source lines** read in this session: `EveryCharacterOfLiteratureOfVWin.lean:220-322` (103); `SiegelEisensteinSecondTermHypotheses.lean:1-108` (108); `ExistsPageN.lean:1-124` (124); `TopPlug.lean:1-57` (57); `SupplyChi.lean:1-54` (54); `ZeroFreeAllOfTopG.lean:1-78` (78); `Hyps.lean:1-125` (125); `At23OfAll.lean:1-59` (59). Directory filename metadata and branch SHA lookups did not read Lean source. No build or CI executed; no local training, QPU, GPU, or cloud compute used.

# RH-26A-01 — bounded dependency trace from GRH to RH

**Date:** 2026-11-23  
**Status:** PASS for the *static top-level dependency-map* rubric; downstream mathematics not yet extracted.  
**Upstream SHA:** `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b` (`leanprover-community/riemann-hypothesis`, `main` at inspection).  
**Local host:** `patrickdugan/MathCan`, `research/rh26-extraction-rubrics-20261123`, draft PR #265.  
**Method:** GitHub file reads only. **No upstream full build, no Lean proof recheck, no mathematical equivalence proved independently in MathCan.**

## 1. Exact output propositions

Source: [Statements.lean:7-20](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Statements.lean#L7-L20), [EveryCharacter.lean:7-8](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean#L7-L8), [HalfPlane.lean:44-51](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean#L44-L51).

- **Half-plane nonvanishing:** for every positive modulus `N` (a `[NeZero N]` instance), complex Dirichlet character `χ` modulo `N`, and complex `s` with `Re(s) > 1/2`, `L(χ,s) ≠ 0`, subject to the sole explicit pair exception `χ = 1` **and** `s = 1`. This is the proposition named `DirichletLNonvanishingRightOfHalf`, and has the same displayed definition as `UpperTheory.EveryCharacter` and `Claim.HalfPlane`.
- **Dirichlet strip statement:** for any such character and `0 < Re(s) < 1`, `L(χ,s)=0` entails `Re(s)=1/2` (`DirichletLZerosOnLine`).
- **Primitive-character strip statement:** the same strip conclusion with an additional `χ.IsPrimitive` hypothesis (`PrimitiveDirichletLZerosOnLine`). This is a corollary of the unrestricted strip result.
- **Zeta:** every zero `s` of `riemannZeta` that is neither a trivial zero `-2(n+1)` for `n ∈ ℕ` nor `s=1` has `Re(s)=1/2` (`RiemannZetaZerosOnLine`). Its Mathlib-facing version is `RiemannHypothesis`. The proof of the equivalence/reducibility of these statement names was not rechecked here.

The phrase “GRH for Dirichlet L-functions” here refers to the second item, for *all* complex Dirichlet characters of nonzero modulus. The first item is the stronger half-plane gateway used to derive it, and the zeta statement is a consequence.

## 2. Dependency graph with source-backed edges

```text
Gal.Int.galoisLocalGlobalStrong_recParameter
     └─► FinalTheorems.everyCharacter_of_row(h : GalStar.Row0b ...)
                 ├─► LiteratureTheorems.every_character_of_literature_of_vWin
                 │       ├─► OpenLiteratureStatements package O
                 │       │     (caraianiLocalGlobalDual := h;
                 │       │      localLanglandsExists := Zero.LLC.recTExists;
                 │       │      galoisRepOfPolarizedPairLit := h)
                 │       ├─► Top.VWin, from One.vwin_of_row(h)
                 │       └─► Lit.every_character_of_theta_integrals_local_matching
                 │             ├─► theta_integrals_agree_and_local_matching ...
                 │             ├─► published_results_eigen / published_results_first
                 │             ├─► self-intersection / volume estimates
                 │             └─► local Langlands existence
                 └─► FinalTheorems.everyCharacter : UpperTheory.EveryCharacter
                            └─► Main.LFunction_ne_zero_of_half_lt_re
                                      ├─► Claim.strip → LFunction_eq_zero_re
                                      │                  └─► primitive variant
                                      └─► Claim.zeta  → riemannHypothesis
                                                        └─► riemannZeta_eq_zero_re
```

### Direct source edges

1. [Main.lean:43-56](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Main.lean#L43-L56) defines all five named headline theorems. The nonvanishing theorem is supplied directly by `UpperTheory.FinalTheorems.everyCharacter`; `Claim.zeta` derives the Mathlib-facing RH theorem; `Claim.strip` supplies Dirichlet strip zeros; the primitive statement is an immediate specialization.
2. [MainConclusion.lean:44-54](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L44-L54) makes `FinalTheorems.everyCharacter_of_row` depend on a `GalStar.Row0b` local-global/reciprocity input `h`. It packages `h` with `recTExists` into the literature interface, adds `One.vwin_of_row h`, and discharges `h` using `Gal.Int.galoisLocalGlobalStrong_recParameter`.
3. [VwinOfRow.lean:42-44](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean#L42-L44) obtains `Top.VWin` from `V.Z.Win.RowT` through `One.Join.automorphic_window_of_inputs` and a base-change theorem. The internal meaning of `Top.VWin` was not inspected in this pass.
4. [EveryCharacterOfLiteratureOfVWin.lean:833-839](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L833-L839) shows the key assembly theorem: from `O : OpenLiteratureStatements` and `hV : Top.VWin`, `every_character_of_literature_of_vWin` obtains `EveryCharacter` by passing theta-integral agreement/local matching, literature packages, a self-intersection/volume-estimate construction, a local Langlands existence input, and `hV` to `Lit.every_character_of_theta_integrals_local_matching`. The exact mathematical internals of the latter are the *next* bounded extraction target.
5. [ClaimStrip.lean:89-130](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L89-L130) provides the reflection step from nonvanishing to the critical-strip conclusion and the zeta conclusion. Its local helper `prim_reflect` transfers a primitive L-function zero at `s` to the inverse-character zero at `1-s`, using completed L-functions and their functional equation ([ClaimStrip.lean:72-87](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L72-L87)). The helper `prim_zero` uses primitive-character reduction and nonzero Euler factors ([ClaimStrip.lean:53-63](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean#L53-L63)).

## 3. Precisely stated input leaf

The named helper `Claim.factor_ne_zero`, [HalfPlane.lean:55-70](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean#L55-L70), establishes the following elementary local fact for a Dirichlet character `ψ`, a prime `p`, and `Re(s)>0`:

```text
1 − ψ(p) · p^(−s) ≠ 0.
```

Its norm estimate uses the strict bound `‖p^(−s)‖ < 1` for prime `p>1` and `Re(s)>0`, together with `‖ψ(p)‖ ≤ 1`. The exact hypotheses are visible in the source. This is one concrete analytic leaf used by the half-plane-to-strip conversion; it is **not** a substitute for the deep global nonvanishing result.

For the deep branch, the formal interface at this boundary is `(O : OpenLiteratureStatements)` and `(hV : Top.VWin)`. Their contents and the hypotheses of `Lit.every_character_of_theta_integrals_local_matching` remain **uninspected**, so no theta-multiplicity exponent or prime-sum estimate is asserted.

## 4. Null model and falsification criterion

A plausible null explanation is that `every_character_of_literature_of_vWin` is an *assembly of large theorem interfaces*, and that apparent simplifications to theta lifts will require extra geometric inputs. A proposed compact operator theorem must show its mathematical hypotheses and recover a quantifiable conclusion under matching normalization. A proof sketch that omits a volume, positivity, local-matching, or Galois assumption fails that gate.

We also have **not located** a source theorem establishing `E(X,m) ≤ C₁X/m + C₂m`. RH-26C is unverified until the exact inequality and parameter dependencies are found.

## 5. Bounded-read receipt and next session

**Eight distinct upstream files inspected** with a source-window budget of approximately **934 lines**, including one-line range probes. The large literature module was inspected in disjoint windows: 1–230, 231–450, 750–840, and nine one-line probes; its middle portion was intentionally left unread. All paths refer to pinned upstream SHA.

**Next bounded target:** locate and read only the declaration/short dependency neighborhood of `UpperTheory.Lit.every_character_of_theta_integrals_local_matching`, plus the definitions `OpenLiteratureStatements` and `Top.VWin`. Start from the exact call at [EveryCharacterOfLiteratureOfVWin.lean:833-839](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L833-L839). Make this a fresh run with its own eight-file cap and ledger checkpoint. Keep RH-26B hypotheses tentative until those definitions and theorem statements are in hand.

**No new Lean source was written or kernel-checked in this run.** This result is an attributed static reading of upstream code only.

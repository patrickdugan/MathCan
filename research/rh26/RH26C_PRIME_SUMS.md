# RH-26C-01: quantitative Chebyshev-window source discovery

**Date:** 2026-11-24 (Asia/Manila)  
**Registration:** [RH26C01_REGISTRATION.md](RH26C01_REGISTRATION.md), committed as `96e28c2cc8d56deb3accbc9dc72626210066259c` before new upstream source reads.  
**Immutable upstream source:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`.  
**Observed upstream main:** `a78183e11ebfeebab77920b5e976f0a3edf1fc76`; no semantic-equivalence claim.  
**Disposition:** **SOURCE DISCOVERY PASS** for a precisely anchored weighted Chebyshev-window theorem and its zero-free consumer. **RH-26C exact X/m+m gate remains UNSOURCED / PARTIAL.** No new Lean kernel check.

## 1. The exact proved quantitative bound

The source declaration `UpperTheory.Comparison₂.core_gm` at [CoreGm.lean:55–58](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L55-L58) establishes the following conditional eventual inequality:

```text
For every Λ : Level and real eD,eL,K,cHH,eK,C,eps with eps > 0,
there exists x1 : ℝ such that for every x >= x1,
every Frame φ, HostAx H for φ, and finite TT ⊆ φ.A:
  EAtH Λ H.toHostRaw TT x eps C
  CoreAtH H.toHostRaw TT eD eL K cHH eK eps x
  imply
  Λ.Gm x <= x^(1/2 + (eD+eL+7)*eps).
```

This is a **one-sided** real inequality. No absolute-value estimate of the displayed aggregate follows from the theorem alone. Its threshold x1 can depend on the fixed level and real parameters listed before the existential; the host and frame are quantified after the threshold. The theorem includes the complete host and core predicates; treating their inputs as arbitrary or removing them would be a different assertion.

At [CoreGm.lean:64–69](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L64-L69), the proof chooses a threshold using `Deduction.ch_core`, `large_x_eventually`, and eventual domination by x^eps. The exact deduction `Deduction.ch_top` is called at [CoreGm.lean:98–104](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L98-L104) with the full size, window and other structural data. It controls a bound containing `errorBracketSizeWindows`. The source subsequently uses `gmA_eq`, `sigA_le`, and an extra x^eps factor to obtain the exponent with +7 ([CoreGm.lean:104–117](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L104-L117)).

The bracket is called with arguments
`Dd.x, Dd.ε, Fintype.card φ.A, TT.card, T2.card, m, Dd.b, Dd.k, Dd.a`
at [CoreGm.lean:91–103](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L91-L103). This is an exact lead to the underlying quantitative estimate, but its definition and the precise `Deduction.ch_top` conclusion were not read in this session. The theorem alone does not identify an error of the form X/m+m.

## 2. What the Chebyshev observable means

Write Lambda_vM(n) for the von Mangoldt weight, to distinguish it from the level object Λ. The actual `An.sumLamChi` and `An.gChi` definitions at [Analytic.lean:56–71](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L56-L71) use the smoothed weight max(y/n-1,0):

```text
Sχ(y) = Σ_(1 ≤ n ≤ floor(y)) Λ_vM(n) χ(n) max(y/n-1,0).
G(y) = Σ_(1 ≤ n ≤ floor(y)) Λ_vM(n) max(y/n-1,0)
       - y(log y - 1 - γ).
gChi(χ,y) = G(y) for the trivial character,
            Sχ(y) + y (L'(χ,1)/L(χ,1)) otherwise.
```

These are smoothed **prime-power** sums, with a logarithmic derivative or principal-character main-term correction. They are not the unsmoothed sum of primes and do not by themselves specify a two-term error model in m.

The level observable is defined at [ExplicitFormulaErrorOfHostConditions.lean:73–80](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L73-L80) as a baseline `Formalism.Gz y` plus a weighted sum of the real parts of `An.gChi` over nontrivial kept primitive characters. The weight is 1 for the distinguished kept exceptional character and 1/(3o+1) otherwise, with o a natural level parameter. The exact relation between `Formalism.Gz` and the other analytic sums requires its own definition; this run does not equate them by name.

## 3. The actual hypotheses and the role of m

The host predicate `EAtH` at [ExplicitFormulaErrorOfHostConditions.lean:180–187](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L180-L187) packages:
- level/order compatibility, kept-character and exceptional-character conditions;
- a finite-set share discrepancy at tolerance x^(-1+eps), whose exact cardinality inequality is at [ExplicitFormulaErrorOfHostConditions.lean:170–176](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L170-L176);
- `BoundedCharsPointwise`, the norm bound on designated characters stated at [Analytic.lean:181–191](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L181-L191) as at most x^(1/2+eps);
- a logarithmic-derivative bound C log x for the appropriate primitive characters.

The other input, `CoreAtH`, is defined at [CoreAtH.lean:69–81](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean#L69-L81). It existentially introduces types and finite indexing data, **m,f : ℕ**, `Dd : Data U0 W Top m f`, constants, a finite T2, weights and compatibility data. It imposes `SizeData₂`, `ErrWindows`, `BNBoundsU`, `SizesA`, `ThinScales`, `CostWindows`, `RestSize` and related bounds.

Thus m is a natural-number parameter of a structured arithmetic family. Its feasible range, relation to x, and effect on constants must be derived from these predicates before treating it as a freely tunable positive real or integer. The final `core_gm` theorem does not expose m as an independent tuning variable.

## 4. Trace to a zero-free conclusion

The family lift `EFamC` requires eventual host conditions uniformly over indices, with existential C and threshold x0 ([TopDefs.lean:50–53](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopDefs.lean#L50-L53)).

`UpperTheory.Comparison₂.windowInequality_of_artinInputs` ([WindowInequalityOfArtinInputs.lean:51–65](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean#L51-L65)) converts the tied-family condition into `FamCoreConstantBounds`, applies `core_gm` with an eligible family index, and obtains the Chebyshev-window inequality.

`Formalism.HC.ChebyshevInequalityOnWindows` at [TopWin.lean:57–66](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean#L57-L66) places the inequality on `(core Fm).Win`. Its zero-free consumer `level_of_tiedWin` ([TopWin.lean:81–94](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean#L81-L94)) chooses a sufficiently small positive eps for a given s with real part above 1/2; the `FormBAt` condition then transfers a window exponent below real part(s) to the zero-free assertion. The source-level implication is conditional on the explicit `FormBAt` premise and existence of suitable windows.

At [TopWin.lean:96–106](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean#L96-L106), the cyclic-character wrapper lifts this implication to `ZeroFreeOn`. The previously traced `zeroFreeAll_of_topG` at [ZeroFreeAllOfTopG.lean:66–74](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean#L66-L74) uses this wrapper with `level_gm_le_on_family_scales` and `formB`. This establishes the position of the quantitative window bound in the top-level proof; the individual sources of those latter two facts are separate dependencies.

## 5. Independent conditional optimization (paper algebra, not upstream evidence)

Assume X>0, A>0, B>0, and m>0, with A,B fixed independently of X,m. If an actual error is bounded above by A X/m+B m, the right-hand side has a unique continuous minimum at r=sqrt(A X/B), since

```text
A X/m+B m-2 sqrt(A B X) = B (m-r)^2/m.
```

For positive integer m, selecting n=ceil(r) yields n≥1, with an excess above the continuous optimum of B(n-r)^2/n≤B/n. The integer minimizer over all positive integers is among max(1,floor(r)) and ceil(r), since the objective decreases before r and increases after r. This choice is feasible only if the source domain admits the selected integer. On a restricted interval, the continuous minimizer is clamped to that interval, and the integer candidates must belong to it. With fixed A,B and an admissible square-root scale, the minimum of this *upper envelope* is O(sqrt X); no matching lower bound on the actual error E follows merely from an upper bound.

This derivation supplies the independent algebra portion of RH-26C. It does **not** establish the existence of the hypothesized bound in the formal argument.

## 6. Disposition, falsifier, and next bounded session

| Target | Status |
| --- | --- |
| Actual upstream weighted Chebyshev exponent | FOUND: `core_gm` |
| Smoothed prime-power and character observables | FOUND |
| Host/core assumptions and natural parameter m | FOUND at interface level |
| Proof use in zero-free window machinery | FOUND |
| Exact `errorBracketSizeWindows` formula, ranges and constants | OPEN |
| Actual X/m+m error theorem | UNSOURCED / PARTIAL |
| Independent optimization identity | PAPER ALGEBRA ONLY |
| New Lean verification | NOT RUN |

The registered null remains plausible. A valid source identification must exhibit both terms, the relevant X and m, the allowed m range, and uniform constants. One must also show how that expression bounds the specific error used by the proof. Matching a square-root exponent or finding any two additive terms is insufficient.

**RH-26C-02 next:** begin with `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` and `ChTop.lean`, the exact imports and call sites in `CoreGm.lean:64,91–103`. Trace the declaration of `errorBracketSizeWindows` and the applicable `RestSize`/size-window assumptions through their direct imports under a fresh eight-file/1,200-line budget. If the formula is not equivalent to the proposed heuristic under the actual domain, record the obstruction without claiming a global negative result. A separate Lean algebra check can be preregistered once the actual envelope is found.

## 7. Read-budget receipt

Eight distinct upstream Lean files at the frozen pin, **918 returned source lines**:

| Source path relative to src/ | Lines |
| --- | ---: |
| `Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean` | 1–78 (78) |
| `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` | 1–191 (191) |
| `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopDefs.lean` | 1–66 (66) |
| `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean` | 1–112 (112) |
| `Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean` | 1–69 (69) |
| `Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean` | 1–117 (117) |
| `Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean` | 1–85 (85) |
| `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean` | 1–200 (200) |

All line requests terminated at file end; no individual file returned more than 250 lines. The two targeted directory filename indexes and ancestor tree traversals did not read other Lean source. No full repository scan, clone, build, independent kernel run, GPU/QPU or paid compute. Runtime and RAM unmeasured.

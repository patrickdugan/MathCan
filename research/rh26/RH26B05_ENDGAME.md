# RH-26B-05 — how leaves supply theta comparison, nonzero scalars, and rank transport

**Registration:** [RH26B05_REGISTRATION.md](RH26B05_REGISTRATION.md), committed before upstream reading.  
**Run date:** 2026-11-23.  
**Immutable source:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`.  
**Upstream main observed at registration:** `98cc3736f046abae883d8cda839c84f3004257a7`, a newer commit. No equivalence audit or silent switch to that revision.  
**MathCan:** `research/rh26-extraction-rubrics-20261123`; draft PR #265.  
**Disposition:** **PASS** for the exact five-part interface, conditional induction structure, and two geometric rank-reduction keys; **PARTIAL** for the completed `kBeta` and `kAlpha` proofs, whose final source lines lie beyond this session's per-file cap. This is a static source trace, with no new Lean kernel proof.

## 1. One-line decomposition of the endgame

The theorem `PositivityTheory.ThKG.agree_of_leaves` at [AgreeOfLeaves.lean:42-49](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/AgreeOfLeaves.lean#L42-L49) concludes the full
`WeilTensorModels.ThetaIntegralsAgree ∧ WeilTensorModels.LocalMatching`.
It does so by pairing two precisely typed constructors:

- `agree_of_parts hd L.kConst hc L.kBeta L.kAlpha` supplies theta-integral agreement.
- `matching_of_parts L.kReal L.kFin` supplies local matching.

Here `L : PositivityTheory.ThKG.Leaves`, `hd : KDecay`, and `hc : KCoinv`. The exact definitions at [MatchingOfParts.lean:46-84](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/Divisors/MatchingOfParts.lean#L46-L84) establish that:

| Input | Formal conclusion and function |
| --- | --- |
| `KDecay` | Every admissible triple gives `Decay`, including its integrability/growth requirements |
| `KConst` | Every matched triple has a `OneConst` witness, including uniqueness and nonzero scalar |
| `KCoinv` | Every matched triple satisfies the `Coinv` quotient/factorization conditions |
| `KBeta` | Separately existential `e₁,e₂,s : ℤˣ`; all number-field settings satisfy `StepBeta` |
| `KAlpha` | Separately existential `e₁,e₂,s : ℤˣ`; all number-field settings satisfy `StepAlpha` |
| `KReal`, `KFin` | Existential real and finite quotient maps separately, assembled as `LocalMatching` |

The `KConst`, `KBeta`, and `KAlpha` contracts exactly fit the original `ThetaIntegralsAgree` conjunction at [WeilTensorModels.lean:623-630](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L623-L630), documented in RH-26B-03. These five inputs are the smallest **source-level interface**, rather than a newly proved analytical compression.

## 2. The strong induction that constructs the nonzero scalar

`Leaves` is a substantial geometric/analytic record at [CtSmallCone.lean:55-81](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L55-L81). It contains rank-tower inputs `towerA`, `towerB`, local lifts `locA/locB`, endgame clauses `endA/endB`, archimedean and finite-place compatibility, and a collection of nonzero/decay/splitting inputs.

At [PolDense.lean:62-70](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/PolDense.lean#L62-L70):

- `Claim` requires **(i)** a nonzero polynomial comparison constant, **(ii)** a test vector with nonzero integral on the first model, and **(iii)** a special-subspace vector with nonzero integral on the second model.
- `Below n` asserts `Claim` for every admissible matched triple with `G.p + G.q < n`.

The main step `Leaves.const_of` at [CtSmallCone.lean:131-179](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L131-L179) takes a lower-rank hypothesis `hB : Below (G.p+G.q)` and constructs `∃ c, c ≠ 0 ∧ PolConst ... c`:

1. If both ranks `G.p` and `G.q` vanish, it invokes `L.polZero` (lines 134–136).
2. If `G.q=0` and `G.p>0`, it uses `towerA`, matches the smaller configurations, obtains `KeyA` and its scalar `C`, then combines `facNe`, the smaller nonzero `c₁`, and `endA` (lines 137–157).
3. If `G.q>0`, it applies `towerB`, `KeyB`, `facNe`, and `endB`, producing a nonzero constant by a divisor with a proved nonzero denominator (lines 158–179).

In the alpha case the scalar is a product of nonzero factors. In the beta case it is a quotient by nonzero factors. **The asymmetry of rank paths is important** for faithful simplification.

The lower-rank hypothesis comes from `Leaves.below`, whose actual proof is induction on a natural number `n` ([CtSmallCone.lean:212-215](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L212-L215)). `Leaves.claim_of` assembles the nonzero test vectors from the constant and matched or anisotropic data ([CtSmallCone.lean:197-210](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L197-L210)). Thus the mathematical mechanism is a *well-founded rank induction with quantitative compatibility obligations*; it is not just an isolated equation of theta integrals.

### Recovering the universal comparison constant

The specific `Leaves.kConst : KConst` declaration is at [CtSmallCone.lean:234-241](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L234-L241). It:

- extracts `Claim` for a matched configuration;
- selects a matched test pair with a nonzero integral evaluation;
- proves any scalar `c'` satisfying the full `IsConst` comparison must equal the already established `c`, by cancellation against a **nonzero** integral;
- invokes `Leaves.isConst_of` ([CtSmallCone.lean:222-232](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L222-L232)) to extend a polynomial comparison to the full test-function `IsConst` assertion through convergence and continuity.

This provides the exact formal supplier of `OneConst`, through `KConst`. The uniqueness proof needs nonzero evaluation and continuity; these are genuinely separate mathematical gates.

## 3. The rank-changing alpha and beta keys

At [CtSmallCone.lean:88-91](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L88-L91), `Leaves.keyB` and `Leaves.keyA` are assembled from the geometric record. Their exact predicates are at [KeyAOf.lean:66-78](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/KeyAOf.lean#L66-L78) and [KeyAOf.lean:119-129](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/KeyAOf.lean#L119-L129):

**Beta key:** with a paired geometry in which the second rank changes by two, `KeyB` yields a nonzero scalar `C`, a local split-component identity involving `C · stepFac · charL`, and a test vector on which the relevant component is nonzero. The source proves `keyB_of` using evaluation-at-zero/cone inputs, a stabilizer, big-zero/small-cone estimates, local beta matching, and Levi decomposition ([KeyAOf.lean:80-113](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/KeyAOf.lean#L80-L113)).

**Alpha key:** a two-rank change in the first space yields `KeyA`, which provides a compatible local split relation and a nonzero test component. Its source `keyA_of` uses evaluation-at-zero/cone, small-zero/big-cone estimates, local alpha matching, Levi decomposition, an anisotropic input, and matching existence ([KeyAOf.lean:131-169](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/KeyAOf.lean#L131-L169)).

The `KeyA` and `KeyB` witnesses include **separately chosen** integer units. Their normalization constants are built from quotients/products of quantities shown nonzero in the source; the same global units need not serve both rank paths.

The complete `kBeta` implementation begins at [CtSmallCone.lean:243-250](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L243-L250), with `L.keyB`, the smaller `Below` induction, a matched test pair, and a split-component witness. The file extends past the 250-line read cap, so **the final `KBeta` construction, and `kAlpha` declaration, were not examined in this run**. Their *existence as members of the Leaves record* is visible at [AgreeOfLeaves.lean:46-47](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/AgreeOfLeaves.lean#L46-L47); their concrete proof bodies require a fresh source window.

## 4. Clarifying `EndA`, `EndB` and the analytic inputs

The proposition `EndB'` at [PolDense.lean:72-77](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/PolDense.lean#L72-L77) takes a matching hypothesis with `1 ≤ G.q` and the smaller-rank `Below` result, then upgrades a **beta split-component identity** to `PolConst`. `EndA'` at [PolDense.lean:79-84](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/PolDense.lean#L79-L84) performs the analogous upgrade when `G.q=0` and `1 ≤ G.p`. The adaptors `endB'_of` and `endA'_of` explicitly obtain these from `GlobalTheory.ThK.EndB` and `EndA` ([PolDense.lean:106-110](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/PolDense.lean#L106-L110)). The earlier hypothesis that these endgame propositions participate in the beta and alpha rank branches is therefore **confirmed at their adapters and uses**, although the full definitions of the more general `EndA/EndB` remain deeper in the source tree.

The rest of `endAB_sph` is a separate construction. At [EndCore.lean:275-295](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/EndCore.lean#L275-L295) it obtains zero-case, low-case, and two-step auxiliary results. Its analytic side includes an explicit `SiegelWeilStd`-driven construction of `SWAniso`, and `EisBL`-driven `EisContinues`, then uses them to build full theta/Siegel–Weil and orthogonality inputs ([EndCore.lean:303-347](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/EndCore.lean#L303-L347)). It ends by producing `EndA` and `EndB` through `PositivityTheory.ThKEnd.endA_of` and `.endB_of` ([EndCore.lean:355-358](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/EndCore.lean#L355-L358)).

The formal analytic input definitions are now pinned:

- `EisBL` ([HypothesesE.lean:85-92](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesE.lean#L85-L92)) universally requests an Eisenstein-series continuation `Ê` with an initial convergence region, differentiability on its right half-plane, and a local pole-clearing condition controlled against continuous moderate-growth linear functionals.
- `SiegelWeilStd` ([HypothesesS.lean:50-60](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesS.lean#L50-L60)) is an **Eisenstein special-value identity** relating `EisValueAt` to a theta integral on an admissible Haar fundamental domain, with ranks, signatures, automorphic character data, and finite-dimensional orbit span conditions. The factor is `1` when `n<m` and `2` otherwise in the displayed theorem.

A replacement operator theorem would need those analytic prerequisites or a new proof of their consequences. In particular, the normalization factor in `SiegelWeilStd` matters when comparing nonzero scalars through alpha/beta steps.

## 5. Exact proof interface graph

```text
EisBL + SiegelWeilStd + global/local geometry
                     │
             endAB_sph → EndA ∧ EndB
                     │            plus tower, cone, match and decay inputs
                     ▼
                    Leaves
                ┌────┴─────┐
                ▼          ▼
          keyA / keyB    matched quotients
                │          │
                ▼          ▼
        rank induction    KReal, KFin
       (const_of, below)
                │
          KConst / OneConst
                │
       kAlpha / kBeta (declaration bodies partially beyond cap)
                │
                ▼
    agree_of_parts(KDecay, KConst, KCoinv, KBeta, KAlpha)
                 + matching_of_parts(KReal,KFin)
                │
                ▼
        ThetaIntegralsAgree ∧ LocalMatching
```

The graph distinguishes **directly observed** edges from the incomplete middle code: `kBeta` and `kAlpha` are referenced by `agree_of_leaves` and `Leaves`, while the final declarations are reserved for RH-26B-06.

## 6. Acceptance and falsifiers

| Requested target | Disposition |
| --- | --- |
| `agree_of_leaves` exact five-part decomposition | **FOUND** |
| `KConst` constructs `OneConst` using induction, uniqueness and convergence | **FOUND** |
| Alpha/beta rank-reduction keys and their `charL` factors | **FOUND** |
| `EndA`/`EndB` conversion into component comparison and induction cases | **FOUND at adapter/use sites** |
| Complete proof bodies of `kBeta` and `kAlpha` | **PARTIAL, bounded at line 250** |
| Analytic `EisBL` and `SiegelWeilStd` contracts | **FOUND** |
| Quantitative theta-lift multiplicity or `X/m+m` prime-sum theorem | **UNSOURCED** |
| New MathCan Lean check or native automorphic replay | **NOT RUN** |

A scalar-normalization compression fails if its induction does not supply a nonzero comparison vector, if its alpha/beta local matching does not respect the split-component identities, or if convergence is insufficient to extend `PolConst` to `IsConst`. A simpler operator-theoretic abstraction is **proposed**, and this session establishes only the source contracts needed to test it.

## 7. Next precise source window

**RH-26B-06:** preregister, then read exactly `src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean:251–500` (up to 250 lines; it may end earlier). Trace `Leaves.kBeta`, `Leaves.kAlpha`, and the step from nonzero split-component witness to `StepBeta`/`StepAlpha` at their exact lines. If the file is shorter, record EOF and stop; only then inspect immediate imported theorem signatures within the fresh eight-file budget.

A subsequent **RH-26E-02** may formalize a rank-indexed scalar-transport graph with a decreasing natural-number measure and adversarial missing-witness controls on MathCan Lean 4.35, using CPU CI. It would remain a finite-dimensional/algebraic toy unless the full analytic hypotheses and native theta data are verified.

## 8. Read budget and resources

**Eight distinct upstream Lean files; 998 source-line windows requested/returned, including the repeated tail of EndCore.** Source was pinned to `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b` throughout. All paths below are relative to upstream `src/`:

| File | Windows and count |
| --- | --- |
| `Development/WeilBound/ThetaLifts/AgreeOfLeaves.lean` | 1–49: 49 |
| `Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/EndCore.lean` | 211–358: 148, 345–358: 14 additional requested lines; 162 requested in total |
| `Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean` | 1–220: 220; 221–250: 30; 250 total, cap reached |
| `Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesS.lean` | 1–64: 64 |
| `Development/WeilBound/ThetaLifts/ConeHypotheses/KeyAOf.lean` | 1–173: 173 |
| `Development/AbelianVarietyTheory/Definitions/Divisors/MatchingOfParts.lean` | 1–86: 86 |
| `Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesE.lean` | 1–100: 100 |
| `Development/WeilBound/ThetaLifts/ConeHypotheses/PolDense.lean` | 1–114: 114 |

Total `49 + 162 + 250 + 64 + 173 + 86 + 100 + 114 = 998`. No upstream repository-wide search, extra proof files, downloads, or full builds were used. All upstream source remains on GitHub; only independently written research commentary is stored in MathCan. No CPU CI, GPU, QPU, paid compute, or kernel recheck in RH-26B-05. Wall time/RAM metrics unmeasured.

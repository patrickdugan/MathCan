# RH-26B-06: completed alpha/beta rank-step proof trace

**Date:** 2026-11-24 (Asia/Manila)  
**Registration:** [RH26B06_REGISTRATION.md](RH26B06_REGISTRATION.md), committed `c83d68bd2375f8a551370462c13bb21eefb267f7` before upstream source reads.  
**Immutable source pin:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`.  
**Observed upstream main:** `90cc2e125ba4b6ca10be17d918857800ba6c39cc`. No semantic comparison with the frozen pin.  
**Disposition:** **PASS — both actual rank-step proof bodies located and their cancellation arguments traced.** New MathCan kernel check NOT RUN. Quantitative theta-lift multiplicity and the X/m+m prime-sum estimate remain UNSOURCED.

## 1. Source boundary closed

The registered read of `src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean:251–500` returned lines **251–280**, the end of the file. The previous RH-26B-05 session read lines 1–250. This completes the source-level audit of `Leaves.kBeta` and `Leaves.kAlpha`. All prior source links below refer to the same frozen upstream commit; no earlier file was fetched again in this session.

The exact types `KBeta` and `KAlpha` are given in [MatchingOfParts.lean:58–64](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/Divisors/MatchingOfParts.lean#L58-L64). They entail separately existential integer-unit triples and the respective full `StepBeta` and `StepAlpha` propositions over the number-field setting. The original statements appear at [WeilTensorModels.lean:597–630](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L597-L630). Their combined supplier is [AgreeOfLeaves.lean:46–47](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/AgreeOfLeaves.lean#L46-L47).

## 2. Beta proof: extract an invertible factor and cancel a nonzero evaluation

The complete declaration spans [CtSmallCone.lean:243–261](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L243-L261). Its first eight lines were inspected in RH-26B-05; lines 251–261 complete the proof in this run.

The source begins with `L.keyB`, which gives a nonzero normalization scalar `C` and the local split-component identity after taking a valid pair of matched configurations. The `Below (G.p+G.q)` input is supplied by `L.below`, and `L.matchEx` and `L.splitEx` provide a matched pair of test vectors and a split of the special-side integral. The earlier `KeyB` definition and proof specify this identity and a nonzero witness in [KeyAOf.lean:66–113](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/KeyAOf.lean#L66-L113).

At lines 251–254, the proof uses `polConst_of` to promote the assumed comparison constant `c` to a pointwise proportionality on the matched test functions. Scaling the split on the second side by `c` supplies the split on the first side. The witness from the beta key then chooses a Levi evaluation at which the relevant first-side beta component is nonzero.

Use fresh scalar names for the independently written algebraic description:

```text
D = C * stepFac(...)
Lval = charL(ν, S₀, ((a - (b+2))/2) + 1)
w = selected evaluation of the second-side beta component

hStep: (D * Lval) * (c * w) = c₁ * w
hWitness: c * w ≠ 0
hFactor: D ≠ 0
```

The displayed scalar identity is the specialized `KeyB` relation. This is a mathematical paraphrase, with exact index and type coercions retained in the pinned original.

At [CtSmallCone.lean:255–261](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L255-L261), the proof obtains `hFactor` from `C ≠ 0` and the first component of `L.facNe`, introduces the inverse witness `u=D⁻¹`, uses its inverse equation, and cancels `w`, which is nonzero because `c*w ≠ 0`.

The independent algebra is

```text
(D * Lval) * (c * w) = c₁ * w
=> D * c * Lval = c₁
=> c * Lval = D⁻¹ * c₁
and D⁻¹ * D = 1.
```

This is precisely the orientation used in `StepBeta` ([WeilTensorModels.lean:597–605](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L597-L605)). The proof of `StepBeta` itself does not require an explicit nonzero hypothesis on the input comparison constants in its statement; its stronger nonzero witness is constructed from the geometric/analytic lower-rank claim. Once the nonzero `c₁` supplied by `OneConst` is available, RH-26E-01 verifies the conditional L-value nonvanishing implication.

## 3. Alpha proof: use the other split component and cancel directly

The complete declaration appears at [CtSmallCone.lean:263–274](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L263-L274). It obtains `L.keyA` and its independently chosen integer units, a constant `C ≠ 0`, and an admissible pair of test functions with a nonzero first split-component evaluation. It uses the lower-rank claim and the smaller comparison constant `c₁`.

The alpha branch uses `L.anAll` to turn the existing polynomial comparison into equality of the integrals on the selected pair. Scaling the given split by `c`, then substituting into the `RelA` relation, yields an equality at the chosen Levi evaluation. Its nonzero witness comes from `KeyA`; see [KeyAOf.lean:115–129](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/KeyAOf.lean#L115-L129) and [KeyAOf.lean:131–169](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/KeyAOf.lean#L131-L169).

Write the independent schematic:

```text
D = C * stepFac(...)
Lval = charL(ν, S₀, ((b+2-a')/2))
w = selected evaluation of the first split component
hStep: c * w = (D * Lval * c₁) * w
hWitness: w ≠ 0
```

Cancel `w` to obtain `c = D * Lval * c₁`, exactly the `StepAlpha` orientation in [WeilTensorModels.lean:608–617](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L608-L617). The original proof ends with scalar cancellation at [CtSmallCone.lean:270–274](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/CtSmallCone.lean#L270-L274). Unlike the beta branch, this conclusion requires no inverse witness for D. Nonzero `c` supplied by `OneConst` then yields L-value nonvanishing, as independently kernel-checked in RH-26E-01.

## 4. Completed source-level dependency cut

The bounded research sequence now connects:

```text
EisBL + SiegelWeilStd
    -> theoremK_head2 -> closeSph
    -> endgame, tower, local and analytic Leaves
    -> KeyA / KeyB (split relations and nonzero witnesses)
    -> Below(n), Claim, nonzero comparison scalar
    -> kConst (continuity, matching, scalar uniqueness)
    -> kAlpha / kBeta (witness cancellation and oriented scalar identities)
    -> agree_of_leaves
    -> ThetaIntegralsAgree ∧ LocalMatching.
```

This graph is a source-level account; it is not a new proof of the upstream analytical and geometric premises. The `Below(n)` measure is the sum of the geometry's signature parameters `G.p+G.q`, not a generic bound on dimension, the number of primes, or a theta-lift multiplicity. Its actual `Claim` requires nonzero test functions on both sides, not just scalar equality ([PolDense.lean:62–70](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/WeilBound/ThetaLifts/ConeHypotheses/PolDense.lean#L62-L70)).

## 5. New mathematical abstraction worth testing

**RH-26E-02 proposal: witness-certified rank descent.** Retain the independently verified RH-26E-01 scalar implications, and formalize an independent algebraic toy that contains the *new* witness gate and well-founded rank transport.

Proposed registered targets, to be frozen in a separate experiment before code:

- **Beta witness cancellation:** over a field, prove `D ≠ 0 ∧ c*w ≠ 0 ∧ (D*l)*(c*w)=c₁*w` implies the existence of `u` with `u*D=1` and `c*l=u*c₁`. Also derive `l≠0` only under the additional premise `c₁≠0`.
- **Alpha witness cancellation:** prove `w≠0 ∧ c*w=(D*l*c₁)*w` implies `c=D*l*c₁`, and nonzero `l` under the additional premise `c≠0`.
- **Rank descent:** use a natural measure and explicitly oriented alpha/beta edges; require decreasing rank and a certified comparison equation at each step. One possible theorem derives nonzero scalars at all reached states from a nonzero base, nonzero edge factors (including the L-values when required for transport), and the corresponding recurrence. Treat the edge nonvanishing as a premise; do not use this induction to manufacture it from itself.
- **Controls:** provide concrete zero-witness counterexamples where the component equality holds but the desired transport conclusion fails; provide a missing-invertibility beta counterexample; and show that dropping nonzero L factors breaks nonzero-scalar propagation. A path that fails to decrease the measure cannot be passed off as a well-founded descent.

A related independent uniqueness lemma can state that two comparison scalars agreeing after multiplication by a nonzero evaluation are equal. Use the existing pinned Lean 4.35 Mathlib environment and an isolated CPU proof/axiom gate. This is still a toy until the actual automorphic witness maps and analytic inputs are verified. No claims about quantitative multiplicity, prime error, hardware, or RH follow from these abstract lemmas alone.

## 6. Acceptance and receipt

| Target | Disposition |
| --- | --- |
| Actual complete `Leaves.kBeta` proof | FOUND, CtSmallCone.lean 243–261 |
| Actual complete `Leaves.kAlpha` proof | FOUND, CtSmallCone.lean 263–274 |
| Nonzero component cancellation and beta inverse gate | FOUND |
| Exact link to previously verified field-level transport | FOUND, conditional |
| Independent Lean verification of the newly isolated witness/rank abstraction | NOT RUN |
| Quantitative theta multiplicity / X/m+m error | UNSOURCED |

**Read budget:** one upstream Lean file, 250 requested lines (251–500), 30 returned lines (251–280, including namespace closure). No further upstream files or directory scans; references to earlier inspected lines were reused from the frozen source ledger. No new CI/kernel check, upstream build, GPU, QPU, paid compute, or memory/runtime measurement.

**Next experiment:** RH-26E-02, independently preregister and implement witness-certified scalar cancellation and rank descent with adversarial controls in MathCan Lean 4.35. Keep it separate from upstream source. RH-26C remains an independent source-discovery track; do not silently replace it with a rank-induction toy.

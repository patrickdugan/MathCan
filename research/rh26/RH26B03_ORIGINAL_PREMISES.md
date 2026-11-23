# RH-26B-03 — original theta-comparison premises and rank-step identities

**Session:** 2026-11-23. **Upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`.  
**Status:** **PASS — exact original premise definitions located**. **Quantitative theta multiplicity remains UNSOURCED**. This is a static source audit and an independent paper-algebra derivation, **not** a Lean kernel verification.

## Read receipt and closed search

Read one file, `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean` lines **501–634** (134 lines). The requested window was 501–750 but the file ends at 634. It was the source boundary registered by RH-26B-02. The upstream branch still pointed to the same pinned commit when checked. No additional upstream Lean file was opened. The namespace closes at lines 632–634, so the **original premise definitions are now recovered** and there is no further continuation in this file.

## Original `WeilTensorModels.LocalMatching`

At [WeilTensorModels.lean L619–L621](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L619-L621), the proposition has the structure:

> For every admissible number-field pair `F,E` with an `F`-algebra structure on `E`, algebra endomorphism `σ`, base datum `B`, ranks `a,a'`, geometry `G`, character datum `X`, and representations `om,om'`, a witness of `IsTriple B G X om om'` entails the existence of `R : RealMaps` and `Rf : FinMaps` satisfying `IsMatched B G X om om' R Rf`.

This is an **existence theorem for compatible quotient representations at all relevant places**. `IsMatched` is a conjunction of `IsTriple`, `IsRealMaps`, and `IsFinMaps` ([WeilTensorModels.lean L531–L534](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L531-L534)). The previous RH-26B-02 report documents the Lie/compact-compatibility and irreducibility requirements in `IsRealMaps`; the completed `IsFinMaps` structure also requires local equivariance, irreducibility, matching nonzero spherical vectors at good places, and special-place zeta conditions ([WeilTensorModels.lean L501–L508](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L501-L508)).

## Original `WeilTensorModels.ThetaIntegralsAgree`

The type at [WeilTensorModels.lean L623–L630](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L623-L630) is a **three-component conjunction**:

1. **Analytic/matching component.** For each admissible `IsTriple` it supplies `Decay`, and for every pair of maps satisfying `IsMatched`, it supplies `OneConst` and `Coinv`.
2. **Beta-step transport component.** There exist global unit parameters `e₁,e₂,s : ℤˣ` such that `StepBeta σ e₁ e₂ s` holds for every number-field pair and suitable `σ`.
3. **Alpha-step transport component.** There exist (potentially different) global unit parameters `e₁,e₂,s : ℤˣ` such that `StepAlpha σ e₁ e₂ s` holds for every number-field pair and suitable `σ`.

The two existential unit triples are **separate** and may have different witnesses. The conjunction packages strong **upstream premises**, ultimately discharged elsewhere in the large proof; locating these declarations alone does not verify their proofs.

### Analytic/matching subpredicates

- `Decay`: admissible theta sums on the first model are integrable; the second model's special vectors have a stated rapid-growth/decay inequality at each exponent `N`, are integrable, and give a moderate-growth integral ([WeilTensorModels.lean L536–L539](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L536-L539)).
- `OneConst`: at least one nonzero theta integral exists for the second model; there is a **unique** scalar `c` giving `Model.I` equality on all `Match` pairs, and **every such scalar is nonzero** ([WeilTensorModels.lean L529–L543](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L529-L543)).
- `Coinv`: at good finite places, the kernels of the finite maps agree with explicitly defined augmentation subspaces on Schwartz functions; image restrictions are surjective for specified local subspaces, and linear functionals killing the augmentation factor through the quotient. A special subspace is stable under the group action ([WeilTensorModels.lean L545–L550](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L545-L550)).
- `Match`: a pair of theta test functions can be approximated through polynomially matched finite sums with a special-side constraint. The `PolMatch` relation compares sums of tensor-product images at a finite set of places ([WeilTensorModels.lean L512–L527](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L512-L527)).

These are mathematical gates for any compression. The named `OneConst` requirement supplies the **nonzero comparison scalars** used below.

## StepBeta: transport equation

At [WeilTensorModels.lean L597–L605](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L597-L605), `StepBeta` considers paired geometric data where the second rank decreases by 2 and the compatible models satisfy the recorded adapted-plane conditions. For a nonzero complex constant `C`, matched maps, and scalar witnesses `c,c₁`:

```text
D := C · stepFac(...)
L := charL(ν, S₀, ((a - (b+2))/2) + 1)
there exists u : ℂ with:
  u · D = 1
  c · L = u · c₁
```

The expressions for `stepFac` explicitly contain ideal characters and local factors constructed from `eps` ([WeilTensorModels.lean L589–L594](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L589-L594)). The quantifiers and the exact index arithmetic must be preserved when lifting a symbolic calculation back into the automorphic proof.

**Exact algebraic consequence** (independent paper derivation, conditional on the quoted identities):

```text
D · c · L = D · (u · c₁) = (u · D) · c₁ = c₁.
```

If `c₁ ≠ 0`, then `L ≠ 0`; otherwise `c · L = 0`, contradicting `u · c₁ ≠ 0`, since `u · D = 1` forces `u ≠ 0`. The `OneConst` predicate gives nonzero scalars for matched maps. This proves an elementary **conditional nonvanishing lemma** for the special L-value in the beta identity. It does not establish the global RH theorem independently.

## StepAlpha: transport equation

At [WeilTensorModels.lean L608–L617](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L608-L617), `StepAlpha` compares paired geometries where the **first** rank decreases by 2, with analogous adapted-plane and matching conditions. The displayed equation is:

```text
D := C · stepFac(...)
L := charL(ν, S₀, ((b+2-a')/2))
c = D · L · c₁
```

Under `c ≠ 0`, this immediately implies `L ≠ 0`. The proof is simply that multiplication by zero would make the right-hand side zero. Its inference uses precisely the scalar nonvanishing supplied by `OneConst`.

**Important distinction:** the beta step has an *explicit inverse witness* `u D = 1`; the alpha step only presents a factorization. Its nonzero `D` follows *under the additional premise* `c ≠ 0` and the displayed factorization. Do not identify the two geometric steps or their `L` arguments.

## Operator-compression hypothesis and control

The relevant algebraic core is now:

```text
   IsTriple ──► LocalMatching ──► compatible RealMaps / FinMaps
        │                                      │
        └──► Decay + Coinv + OneConst ──► nonzero scalar comparisons
                                                │
                            StepAlpha / StepBeta transport identities
                                                │
                            conditional nonvanishing of special L-values
```

A small MathCan lemma can faithfully isolate scalar transport. To reconnect it to the original theta proof requires the hard geometric data, compatible quotient maps, convergence, uniqueness and existence of comparison scalars, and the actual `StepAlpha`/`StepBeta` hypotheses.

**Proposed RH-26E scalar-transport gym:** using fresh MathCan Lean 4.35 code and a pinned CPU CI run, prove (a) `u*D=1 ∧ c*L=u*c₁ ∧ c₁ ≠0 ⇒ L ≠0`; (b) `c=D*L*c₁ ∧ c ≠0 ⇒ L ≠0`; (c) the normalized beta identity `c₁=D*c*L`; and (d) explicitly register counterexamples when the relevant nonzero premise is removed. Distinguish a new Lean kernel-checked toy lemma from a source-level consequence.

A more speculative *closed-loop control* could check products of alpha/beta transport factors when two **actual matching** rank paths return to identical data. Algebraically the closed product must be 1 when its starting scalar is nonzero. Whether such closed loops exist within the automorphic hypotheses remains **UNTESTED**.

## Results, falsifiers, and next source work

| Target | Disposition |
| --- | --- |
| Original `LocalMatching` declaration | **FOUND**, source lines 619–621 |
| Original `ThetaIntegralsAgree` declaration | **FOUND**, source lines 623–630 |
| Identifiable alpha/beta special-value identities | **FOUND**, lines 597–617 |
| Explicit global theta-lift multiplicity theorem with exponent | **UNSOURCED** |
| Conjectured `X/m+m` prime-sum formula | **UNSOURCED** |
| Independent MathCan kernel check | **NOT RUN** |

A proposed compression is **falsified** if the model omits one of the conditions needed to produce a nonzero `IsConst` scalar, or if its quotient maps fail `IsMatched` while the model assumes the rank-step identities. A numerical coincidence involving theta integrals is not sufficient evidence.

**Next session:** RH-26E-01 as a **source-only registered** scalar-transport Lean/CPU fixture with explicit counterexamples, then a pinned MathCan CI proof audit. A separate RH-26B-04 path should find the *actual proof suppliers* of `StepAlpha`, `StepBeta`, and `OneConst` by tight, indexed symbol/path queries. Preserve this file and `LEDGER.md` as restart points; avoid scanning the entire upstream formalization.

**Resource receipt:** exactly one upstream source file, **134 lines**; no local build, upstream inference, paid compute, GPU, QPU, or GitHub Actions run. Memory and elapsed time were not measured.

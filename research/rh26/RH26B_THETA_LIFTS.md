# RH-26B-01 — theta quotient comparison and two/three-place error term

**Date:** 2026-11-23  
**Pinned upstream:** `c900e67c2fcd1fdb041685820bbd2b867fbc5a4b`  
**Protocol status:** SOURCE DISCOVERY PASS; mathematical toy PASS (independently derived, not kernel-checked); **RH-26B quantitative multiplicity extraction remains BLOCKED / UNSOURCED**.  
**Host:** MathCan draft PR #265, branch `research/rh26-extraction-rubrics-20261123`.

## The exact source-level distinction

Two predicate families must be kept distinct:

1. `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree` and `...LocalMatching` are upstream **premises** of the two twisted conversion theorems. Their original full definitions have **not been inspected** in this run. The first 250 lines of [WeilTensorModels.lean:48-250](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L48-L250) construct background adelic, Weil and theta objects but do not yet give the required predicate signatures.
2. `GlobalTheory.SquareSt.ThetaIntegralsAgree` and `...LocalMatching` are **output statements** defined directly at [ThetaIntegralsAgree.lean:60-80](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Statements/HeckeThetaIntegrals/ThetaIntegralsAgree.lean#L60-L80). These are the quantifiers and operators recovered in this run. Substituting these outputs for the upstream premises in a simplified proof would be an unjustified type change.

## B1. Output theta-integral agreement

The output proposition `SquareSt.ThetaIntegralsAgree` ([ThetaIntegralsAgree.lean:73-80](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Statements/HeckeThetaIntegrals/ThetaIntegralsAgree.lean#L73-L80)) quantifies over `D : D7`, an additive adelic character `ψ`, a chosen infinite-family `θ` satisfying `IsInfFam`, Hermitian spaces `W,W₁,X` with frames `A,A₁,B`, characters `α,β` satisfying `IsTriple`, Haar/fundamental-domain data, and matching Weil-theta representation data `IsMatch`. It then asserts the existence of a **nonzero scalar** `c : ℂ` such that for any allowed `Φ'` there exists a representative `Φ₀` satisfying:

- `Φ' - Φ₀` belongs to the finite-relation subspace `finRel`;
- `Φ₀` has the required `ModInt` convergence;
- for each allowed `Φ` with matching image `p Φ = p' Φ₀`, `thetaInt_A(Φ) = c • thetaInt_B(Φ₀)`.

The theorem `GlobalTheory.SquareAgree.twisted_theta_integrals_agree` ([TwistedSquareThetaIntegralsEq.lean:57-81](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSquareThetaIntegralsEq.lean#L57-L81)) derives that output from `ThetaLocalInputs`, **upstream** theta-integral agreement, and upstream local matching. Its proof gets a placewise seesaw triple and matching quotient data, compares theta kernels **up to a nonzero scalar** `s`, and forms `c * s`. It uses a coinvariant passage and a moderate-growth result to obtain admissible representatives and convergence. The adapter `GlobalTheory.T.twisted_square_theta_integrals_eq` is at [TwistedSquareThetaIntegralsEq.lean:88-90](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSquareThetaIntegralsEq.lean#L88-L90).

**Compression target:** identify the minimal assumptions ensuring a nonzero scalar comparison **on the quotient by finite relations**, while keeping convergence and local normalization explicit. The scalar is an existence conclusion; no canonical value or global phase was established.

## B2. Local-matching tensor factorization

The output proposition `SquareSt.LocalMatching` ([ThetaIntegralsAgree.lean:60-71](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Statements/HeckeThetaIntegrals/ThetaIntegralsAgree.lean#L60-L71)) asks for a common complex module `Pr` and surjective linear maps from the two polynomial Fock spaces to `Pr`. Under the triple and exponent hypotheses and `IsMatch`, it produces another complex module `Pf`, linear maps from the two oscillator-function spaces onto `Pf` (in the stated finite-function sense), and a linear equivalence

`e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi`.

It requires each matched map on a Fock-generated function to factor as the image of a pure tensor through `e`. The existence and surjectivity requirements are substantive: equality of integrals alone does not force them.

The source theorem `GlobalTheory.SquareLM.twisted_square_local_matching` ([TwistedSquareLocalMatching.lean:55-118](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSquareLocalMatching.lean#L55-L118)) obtains common polynomial quotient data using `twisted_quotient_real`; invokes a Dixmier commutant/scalar argument under irreducibility; forms finite-Fock submodules `S,S'`; and uses `GlobalTheory.SquareLM.productForm` to construct `Pf` and the tensor equivalence. It then extends the constructed maps to the whole function space. The adapter `GlobalTheory.T.twisted_local_factors_match` is at [TwistedSquareLocalMatching.lean:125-127](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSquareLocalMatching.lean#L125-L127).

Matching triples themselves are constructed conditionally in `GlobalTheory.TripleRead.triple_exists_matching` ([TripleExistsMatching.lean:53-63](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TripleExistsMatching.lean#L53-L63)), using Weil square commutation, Darboux coordinate choices and `exists_matching_triple_for_theta_lift`. Its result is a matched-data witness for the triple; its existence does not prove a multiplicity or dimension estimate.

**Potential operator reduction:** regard `Pr` and `Pf` as the common quotient modules and `e` as the compatibility isomorphism. A simplified theorem must preserve the surjectivity/irreducibility hypotheses, purity of the tensor factorization, and the relevant local data. An arbitrary linear integral identity does not imply this structure.

## B3. Exact local arithmetic inequality

The predicate `GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt` ([BoundAtTwoThreeFamilyFon.lean:60-65](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BoundAtTwoThreeFamilyFon.lean#L60-L65)) says that there exist real constants `C` and `x₀` such that for all `x ≥ x₀`, all family indices, Hermitian/local functional data and hub data satisfying `SetupAlt`, `BoundAtTwoThree (L, X.ρ, C)` follows.

The `SetupAlt` record ([BoundAtTwoThreeFamilyFon.lean:50-58](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BoundAtTwoThreeFamilyFon.lean#L50-L58)) demands norm-choice facts, canonical row data, admissible/polynomially bounded parameters, `8 ≤ L.sc.L`, `60 ≤ D.host.splitBound`, a killing condition on the hub representation, and odd-place Tate–Shafarevich finiteness. For the row input, [BoundAtTwoAndThreeForFamily.lean:62-64](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoAndThreeForFamily.lean#L62-L64) defines `rowC(C₂)` with fixed numeric entries 320, 25, 23, 32 and 32.

The underlying `BoundAtTwoThree` condition ([BoundAtTwoThreeFamily.lean:87-88](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L87-L88)) applies to twisted local indices at residue prime 2, or at 3 when 3 lies outside `D.host.small`. For each good component `π`, it requires `Bd ρ i π (midF L C)`, where [BoundAtTwoThreeFamily.lean:52-54](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L52-L54) defines

```text
  vcc(i,π) ≤ sPi(i,ρ(i),π) + midF(L,C)
              + VVr(D,l(i)) + vhE(D,l(i)) + epsL(l(i)).
```

The exact error term at [BoundAtTwoThreeFamily.lean:68-69](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L68-L69) is

```text
midF(L,C) = C·D.R.f·D.R.m·L.sc.b·log(L.sc.x)
          + C·(L.sc.x)^C·(large₂(L))².
```

The same module proves `midF_mono` in `C` for `C ≤ C'` and `0 ≤ C'` ([BoundAtTwoThreeFamily.lean:71-85](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L71-L85)). Separate conditions `MultLe`, `StarS`, `StarG`, and `StarH` occur later ([BoundAtTwoThreeFamily.lean:90-124](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L90-L124)), and `Concl` includes `MultLe`, `num`, `two`, `ram`, and `small` among its constraints ([BoundAtTwoThreeFamily.lean:154-169](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean#L154-L169)). The present `BoundAtTwoThreeFamilyFonAlt` interface alone does not provide a bound of the form `X/m+m`.

**Interpretation:** this is a comparison of local valuation/conductor-style terms, with two explicit additive growth contributions, in a conditioned family. Its symbols, hypotheses and indexing differ from a one-parameter prime-sum error statement. The research target must remain source-specific.

## B4. Independently derived finite-dimensional toy

Take complex one-dimensional vector spaces `A = B = P = U = V = Q = ℂ` and identity quotient maps `q, q', r, r'`. Let `e : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ` be the standard multiplication equivalence. Define `I_A(a,u) = c·a·u`, `I_B(b,v) = b·v` for any fixed `c ≠ 0`.

Whenever `q(a)=q'(b)` and `r(u)=r'(v)`, the identities force `a=b` and `u=v`; hence `I_A(a,u)=c·I_B(b,v)`. The tensor images agree under `e` because both are `a·u`. The algebraic proof is elementary substitution and multiplication in `ℂ`.

**Disposition: TOY, mathematical derivation only.** This illustrates the compatibility square with a nonzero scalar and a common tensor image. It has no automorphic-space convergence, Weil representation, cohomology, or theta multiplicity and was not kernel-checked. It does not count as an independent verification of any upstream theorem.

## Acceptance/falsifier and future run

- **Source discovery:** PASS. The exact `SquareSt` integral/matching output types and the local two/three-prime inequality are source located and paraphrased.
- **Full RH-26B extraction:** BLOCKED / UNSOURCED. No declaration of a quantitative theta-lift vanishing or multiplicity theorem with a derived exponent has been identified; the original `WeilTensorModels` premise signatures remain unread.
- **Falsifier:** an operator reduction that proves only a scalar equality yet cannot construct a common quotient and `HypsAlt` witness with the linked bounds fails to replace the established interface.
- **RH-26C `X/m+m`:** UNSOURCED. No identification with `midF` is justified.
- **Independent kernel audit:** NOT RUN. The pinned MathCan Lean toolchain stays untouched.

**Next fresh bounded run RH-26B-02:** locate the original declaration ranges in `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean` using 250-line windows across sessions. Recover `WeilTensorModels.ThetaIntegralsAgree` and `.LocalMatching` exact quantifiers, especially any recursion law or multiplicity condition. Trace the immediately adjacent source of any quantitative inequality only after finding its symbol. Record a new source ledger and stop before context exhaustion.

## Read-budget receipt

Upstream SHA held fixed throughout. The eight distinct source files and fetched ranges were:
1. `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSquareThetaIntegralsEq.lean:1-90` (90 lines).
2. `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSquareLocalMatching.lean:1-127` (127 lines).
3. `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BoundAtTwoThreeFamilyFon.lean:1-68` (68 lines).
4. `Development/AbelianVarietyTheory/Statements/HeckeThetaIntegrals/ThetaIntegralsAgree.lean:1-84` (84 lines).
5. `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean:1-177` (177 lines).
6. `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoAndThreeForFamily.lean:1-78` (78 lines).
7. `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:1-250` (250 lines).
8. `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TripleExistsMatching.lean:1-82` (82 lines).

**Total: 956 source lines; eight upstream files.** Reads were targeted by the previous ledger and direct imports, with no recursive repository scan. GitHub metadata and external commentary were consulted only for navigation, and this report's mathematical claims are anchored to the pinned primary source. No local cloud CPU, GPU, QPU, or Lean build was executed; RAM and wall time were not measured.

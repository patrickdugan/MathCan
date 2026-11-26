# TRR-01: translation-rank rigidity

## Security evaluation: TRR-12

[TRR-12](trr12/README.md) connects the interpolation results to a concrete
ECDSA risk assessment and a preregistered evaluation program. Its exact
control gives an O(log q)-gate circuit for the forward decoder despite the
large minimum ordinary polynomial degree. All 130,464 circuit evaluations
pass on six toy curves, including every assigned identity value. The
[risk assessment](trr12/ECDSA_RISK_ASSESSMENT.md) states the missing
resource-preserving reduction, separates recovery and signer risks, and
reviews current quantum and migration evidence. New circuit identities
retain a written proof and finite verification boundary.

## Current formalization: TRR-11

[TRR-11](trr11/README.md) proves the exact ordinary degree `ceil(N/3)` for actual four-variable coordinate decoders on arbitrary smooth generalized Weierstrass models with finite odd marked order `N>=19`, when `2`, `3`, and `N` are nonzero in the field. The theorem covers arbitrary fields, including finite extensions and odd composite orders. The combined Lean audit checks 217 principal reports. Exact coordinate controls cover 22,186 generalized models and retain 106 decoder coefficient witnesses. The [proof review](trr11/proof_review.md) records the remaining matching-characteristic and small-order formal work.

[TRR-10](trr10/README.md) supplies the exact degree theorem on short models and its explicit point-mass construction. TRR-11 proves the point-group equivalence and the degree-preserving coordinate transfer, including the assigned identity value.

[TRR-09](trr09/README.md) supplies the actual residue eigenvector exclusion. The earlier [TRR-08](trr08/README.md) layer connects the degree-eight obstruction to Mathlib's curve points and supplies the finite tensor and affine point-ideal groundwork.

## Uniform result and experiments: TRR-07

[The uniform interpolation theorem and experiment suite](trr07/README.md) establish the exact affine-block degree `ceil(N/3)` for every prime subgroup order `N>=7` in characteristic zero or greater than three. A degree-eight obstruction closes every order from nineteen onward; the earlier integral certificates cover 7, 11, 13 and 17. The suite includes extension-field sweeps, exact robustness distances, independent certificate replays and fifteen new Lean field-algebra theorems. [The complete uniform argument](trr07/uniform_probe.md) and [independent proof review](trr07/uniform_proof_review.md) state the geometric premises and formalization boundary.

The sections below preserve the earlier research stages and their verification records.

**Evidence status:** written proofs and exact finite computation, with sixteen TRR-01 supporting theorems checked by Lean 4.35.0 in [CI](https://github.com/patrickdugan/MathCan/actions/runs/45600455877) and locally. The TRR-03 extension adds six locally checked finite-witness theorems. The mathematical scope is specified below.

[Corrected audit](AUDIT.md) develops the finite-field counting theorem and its equality case, the sharp cyclic reducibility threshold with the binary rank-two exception, rational-function pole stability with separate degree and rational-pole budgets, Cauchy clean-submatrix stability, the m-sequence aperiodicity radius, and a counterexample to the unrestricted spectral claim. The original user-supplied derivation is audited, not presented as independent peer-reviewed work. The cited character-sum result remains conditional on the required nondegeneracy hypotheses.

## Verification and scope

Run `python research/translation_rank_rigidity/verify_rigidity.py` from the repository root. This standard-library verifier regenerated receipt.json byte-for-byte on 2026-11-25. It checks 270849 degree partitions, 32768 binary functions on C15, 392 Cauchy minors and all 244 rational points of the explicit elliptic counterexample. The three imported files match their sandbox Git blob hashes. No original Windows scripts were available.

The Init-only module `MathCan/TranslationRankRigidity.lean` proves finite pigeonhole counting via explicit base-Q coordinate encodings and the Hamming triangle/permutation lemmas, then bounds the distance of any periodic approximation. These are supporting statements for the counting and period-stability theorems. The map from a finite-field translate module into a coordinate orbit, finite-field equality characterization, irreducibility threshold, algebraic-curve pole relations, Cauchy determinants and character-sum estimates remain written mathematics. The clean-block and pole-budget lemmas formalize arithmetic steps conditional on the corresponding combinatorial and geometric hypotheses. CI and a subsequent local run accepted all sixteen theorems; their printed transitive axioms contain only `propext` and/or `Quot.sound`. The module uses Init without Mathlib or admitted proofs.

For a finite enumeration permuted by a shift, if g is fixed by that shift, the triangle inequality gives d_H(f,f∘shift)≤2d_H(f,g), independent of the value field. For a binary m-sequence with n≥2 this implies the lower bound 2^(n-2) for distance to any nontrivially periodic function using the autocorrelation identity established in AUDIT.md. The exact even-n equality and other rank conclusions remain written proofs.

## TRR-02: prescribed cyclic periods

[Minimum-rank theorem and proof](trr02/README.md) and [finite verification receipt](trr02/receipt.json) extend the counting result to prescribed tame and wild cyclic periods. The independent standard-library verifier checks 1,600 divisor-DP comparisons and exhaustively enumerates 114,587 words. The theorem has a written proof. The first TRR-01 CI run passed the Python receipt but failed elaboration of the base case of `encodeDigits` (`decide` on an open goal `0 < Q^0`). The explicit proof `Nat.zero_lt_succ 0` repaired this; [the subsequent CI run](https://github.com/patrickdugan/MathCan/actions/runs/45600455877) confirmed both the kernel check and both exact receipts.

## TRR-03: polynomial decoders and an exact small-order classification

[Polynomial decoder theory and proofs](trr03/README.md) continue Strategy V. They establish sharp monomial bounds, a stronger bound charging the pole divisor of rational features, and a two-value theorem for the degree needed to decode translated x-coordinates from affine coordinates on prime-order subgroups. A residue vector decides the lower value. The order-five exceptional family is classified, and an integer polynomial certificate excludes the degree drop at order seven. [The concrete Mythos prompt](trr03/MYTHOS_PROMPT.md) presents the remaining order-eleven system.

The exact scan covers 74,828 nonsingular curve models over prime fields through 101 and all 70,652 prime-order subgroup instances of order at least five in those models. Its 290 exceptions all have order five. Separate verifiers cover cyclic sharpness, affine evaluation spaces, and the symbolic certificates. These finite ranges are recorded in the receipts.

`MathCan/TranslationPolynomialDecoder.lean` checks the order-five witness over F11. All 25 decoder identities and all 25 curve additions are verified, along with the curve equations, inverse residues, an off-curve identity sentinel, and a nonzero 2x2 minor. Six theorem reports contain only `propext` or no axioms. General rank and algebraic-geometry theorems remain written proofs. The polynomial degree bounds define the present security-research scope; general algorithmic lower bounds require further reductions.

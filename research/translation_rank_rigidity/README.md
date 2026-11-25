# TRR-01: translation-rank rigidity

**Evidence status:** written proofs and exact finite computation; Lean candidate awaiting kernel CI. No claim about cryptographic security or general circuit lower bounds.

[Corrected audit](AUDIT.md) develops the finite-field counting theorem and its equality case, the sharp cyclic reducibility threshold with the binary rank-two exception, rational-function pole stability with separate degree and rational-pole budgets, Cauchy clean-submatrix stability, the m-sequence aperiodicity radius, and a counterexample to the unrestricted spectral claim. The original user-supplied derivation is audited, not presented as independent peer-reviewed work. The cited character-sum result remains conditional on the required nondegeneracy hypotheses.

## Verification and scope

Run `python research/translation_rank_rigidity/verify_rigidity.py` from the repository root. This standard-library verifier regenerated receipt.json byte-for-byte on 2026-11-25. It checks 270849 degree partitions, 32768 binary functions on C15, 392 Cauchy minors and all 244 rational points of the explicit elliptic counterexample. The three imported files match their sandbox Git blob hashes. No original Windows scripts were available.

The Init-only candidate `MathCan/TranslationRankRigidity.lean` proves finite pigeonhole counting via explicit base-Q coordinate encodings and the Hamming triangle/permutation lemmas, then bounds the distance of any periodic approximation. These are supporting statements for the counting and period-stability theorems. The map from a finite-field translate module into a coordinate orbit, finite-field equality characterization, irreducibility threshold, algebraic-curve pole relations, Cauchy determinants and character-sum estimates remain written mathematics rather than Lean results. The clean-block and pole-budget lemmas formalize arithmetic steps conditional on the corresponding combinatorial and geometric hypotheses. No Lean executable was present in the sandbox; CI is the first elaboration check. The module deliberately avoids Mathlib and admitted proofs.

For a finite enumeration permuted by a shift, if g is fixed by that shift, the triangle inequality gives d_H(f,f∘shift)≤2d_H(f,g), independent of the value field. For a binary m-sequence with n≥2 this implies the lower bound 2^(n-2) for distance to any nontrivially periodic function using the autocorrelation identity established in AUDIT.md. The exact even-n equality and other rank conclusions remain written proofs.

## TRR-02: prescribed cyclic periods

[Minimum-rank theorem and proof](trr02/README.md) and [finite verification receipt](trr02/receipt.json) extend the counting result to prescribed tame and wild cyclic periods. The independent standard-library verifier checks 1,600 divisor-DP comparisons and exhaustively enumerates 114,587 words. The theorem is a written proof, not a Lean formalization. The first TRR-01 CI run passed the Python receipt but failed elaboration of the base case of `encodeDigits` (`decide` on an open goal `0 < Q^0`); the candidate now supplies the explicit proof `Nat.zero_lt_succ 0`. Kernel confirmation of the repair remains pending.

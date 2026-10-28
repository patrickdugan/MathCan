# MathCan

Computational and formal investigations of integer exponent notation, rare prime patterns, finite-field polynomial primes, and infinite sequences.

## Graham–Carrot series

- [Investigation 02](graham-carrot/README.md): shifted power twin-prime candidates, finite-field certificates, local singular series, parity filters, and exact versus rounded powers.
- [Verification code](graham-carrot/verify.py): reproducible small-degree and finite-sieve experiments using only Python's standard library.

## Epistemic labels

- **THEOREM**: statement with a supplied proof or precisely stated classical theorem.
- **CHECKED**: finite computation with explicit inputs.
- **CONJECTURE**: unproved infinite claim.
- **HEURISTIC**: quantitative expectation conditional on a model.

An admissible polynomial pair is not automatically a proven infinite twin-prime family. Exponentially large notation gives exact finite integers; a quantified infinite theorem requires separate argument.

## Next gates

1. Verify per-prime local root counts of `(x^(3^m)-4)(x^(3^m)-2)`.
2. Compute certified finite Euler factors and tail experiments.
3. Test Bateman–Horn predictions for several fixed small exponents.
4. Develop Lean statements of CRT survivor counting, factorization obstruction, and binomial irreducibility.
5. Investigate uniformity as exponent and sieve cutoff vary.

Research status: exploratory, independent review needed for new claims.

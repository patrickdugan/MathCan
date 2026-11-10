# MathCan

Computational and formal investigations of integer exponent notation, rare prime patterns, finite-field polynomial primes, infinite sequences, observable-state quotients, market mechanisms, and geometric invariants.

## Mathematics imported as research questions from the *verse* corpora

The first research batch (November 10, 2026) develops new MathCan derivations and exact digital checks from problems exposed by the source indexes. Links to a researcher's work identify motivation. Mathematical claims in these modules belong to MathCan unless a specific external theorem is cited.

| Series | Mathematical content | Verification |
| --- | --- | --- |
| [LVR-01: Intervention quotients](research/levinverse/INTERVENTION_QUOTIENTS.md) | Finite future-test equivalence; interface monotonicity; adaptive stochastic history error `≤1-(1-ε)^T`; cumulative reward bound | 5 Python tests, including 5,832 exhaustive finite cases; six Lean kernel lemmas |
| [CHTR-01: Cycle potentials](research/chitraverse/INTERVAL_CYCLE_POTENTIALS.md) | Directed no-profitable-cycle iff positive node potentials exist; rational max-product Bellman–Ford; interval-rate certificates; concave marginal conversions | 5 Python tests, including 4,096 complete three-node configurations |
| [GFR-01: Gram holonomy](research/goodfireverse/GRAM_HOLONOMY.md) | Positive-definite Gram counterexample; pairwise projector information gap; triple-projector invariant; gauge-covariant holonomy | 3 Python tests, with exact rational 2×2 transport and all sign gauges |

The provenance and a [research continuation ledger](research/VERSE_LEDGER.md) track which links are verified source references, which statements have proofs, and what remains conjectural.

### Check the math

```sh
python -m unittest discover -s tests -v
python graham-carrot/verify.py
lake build MathCan
lake env lean MathCan/Intervention.lean
```

Python 3.10+ and its standard library suffice for the rational oracles. The Lean library uses the pinned Lean 4 toolchain and `Init`, without a Mathlib dependency. GitHub Actions checks both tracks on each PR. Successful finite tests are evidence about the finite implementation; Lean's kernel checks apply only to the six `MathCan/Intervention.lean` lemmas. The stochastic, financial, and Gram theorems currently have human-readable proofs and finite oracles, not Lean formalizations.

## Graham–Carrot series

- [Investigation 02](graham-carrot/README.md): shifted power twin-prime candidates, finite-field certificates, local singular series, parity filters, and exact versus rounded powers.
- [Verification code](graham-carrot/verify.py): reproducible small-degree and finite-sieve experiments using only Python's standard library.

## Epistemic labels

- **THEOREM**: statement with a supplied proof or precisely stated classical theorem.
- **LEAN-CHECKED**: proof elaborated and checked by the pinned Lean kernel with a transitive-axiom report.
- **CHECKED**: finite computation with explicit inputs, not an infinite proof.
- **CONJECTURE**: unproved claim.
- **HEURISTIC**: quantitative expectation conditional on a model.

An admissible polynomial pair is not automatically a proven infinite twin-prime family. Exponentially large notation gives exact finite integers; a quantified infinite theorem requires separate argument.

## Next gates

The original number-theory agenda remains active: verify local root counts; compute certified Euler factors; test small fixed-exponent Bateman–Horn predictions; develop Lean statements of CRT survivor counting, factorization obstruction and binomial irreducibility; and examine uniformity across exponent and sieve cutoff.

For the new series, the next tasks are to formalize the finite partition-refinement bound, the max-product potential theorem, and the Gram triple invariant in Lean, then establish hypothesis-level empirical tests with frozen provenance. See the ledger for the mathematical statements and separation of synthetic evidence from research claims.

Research status: exploratory. Every new scientific claim requires independent review and a domain-specific evaluation protocol.

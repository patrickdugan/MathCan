# MathCan

Computational and formal investigations of integer exponent notation, rare prime patterns, finite-field polynomial primes, infinite sequences, observable-state quotients, market mechanisms, and geometric invariants.

## Mathematics imported as research questions from the *verse* corpora

The first research batch (November 10, 2026) develops new MathCan derivations and exact digital checks from problems exposed by the source indexes. Links to a researcher's work identify motivation. Mathematical claims in these modules belong to MathCan unless a specific external theorem is cited.

| Series | Mathematical content | Verification |
| --- | --- | --- |
| [LVR-01: Intervention quotients](research/levinverse/INTERVENTION_QUOTIENTS.md) | Finite future-test equivalence; interface monotonicity; adaptive stochastic history error `≤1-(1-ε)^T`; cumulative reward bound | 5 Python tests, including 5,832 exhaustive finite cases; six Lean kernel lemmas |
| [CHTR-01: Cycle potentials](research/chitraverse/INTERVAL_CYCLE_POTENTIALS.md) | Directed no-profitable-cycle iff positive node potentials exist; rational max-product Bellman–Ford; interval-rate certificates; concave marginal conversions | 5 Python tests, including 4,096 complete three-node configurations |
| [CHTR-02: Weighted Hodge certificates](research/chitraverse/WEIGHTED_HODGE_ARBITRAGE.md) | Exact minimum-energy obstruction `E=(Cq)ᵀ(CW⁻¹Cᵀ)⁻¹(Cq)`; sharp interval certificates for unicyclic graphs; gauge invariance | 7 exact-rational Python tests, general path-gauge Lean theorems |
| [GFR-01: Gram holonomy](research/goodfireverse/GRAM_HOLONOMY.md) | Positive-definite Gram counterexample; pairwise projector information gap; triple-projector invariant; gauge-covariant holonomy | 3 Python tests, with exact rational 2×2 transport and all sign gauges |
| [CHTR-03: Stateful hook holonomy](research/chitraverse/STATEFUL_HOOK_HOLONOMY.md) | State-expanded max-product potentials; frozen-snapshot false negative; path-ordered gauge curvature; sound state abstraction; robust rate bounds | 10 Python regression tests, including 625 exhaustive 2-state networks and nonlinear reserve checks; 7 Lean additive path lemmas (CI pending) |

The provenance and a [research continuation ledger](research/VERSE_LEDGER.md) track which links are verified source references, which statements have proofs, and what remains conjectural.

### Check the math

```sh
python -m unittest discover -s tests -v
python graham-carrot/verify.py
lake build MathCan
lake env lean MathCan/Intervention.lean
lake env lean MathCan/Hodge.lean
lake env lean MathCan/HookState.lean
```

Python 3.10+ and its standard library suffice for the rational oracles. The Lean library uses the pinned Lean 4 toolchain and `Init`, without a Mathlib dependency. GitHub Actions checks both tracks on each PR. Successful finite tests are evidence about the finite implementation; Lean's kernel checks apply only to the six `MathCan/Intervention.lean` lemmas. The stochastic, financial, matrix Hodge, and Gram results currently have human-readable proofs and finite oracles. The Lean kernel checks the intervention and additive path-gauge lemmas.

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

For the new series, the next tasks are to formalize the finite partition-refinement bound, the max-product potential theorem, and the Gram triple invariant in Lean, followed by the rational weighted Hodge projection identity and its uncertainty bounds, then establish hypothesis-level empirical tests with frozen provenance. See the ledger for the mathematical statements and separation of synthetic evidence from research claims.

Research status: exploratory. Every new scientific claim requires independent review and a domain-specific evaluation protocol.

The CHTR-03 finite hook-state results add a separate directed-automata setting. The full multiplicative potential equivalence is proved in the research note and exhaustively tested on small instances. Lean formalizes its additive path-gauge and potential soundness lemmas; see the note for the remaining formalization gap.

## CHTR-04: Amount-aware funded hooks (2026-11-10)

[Research note](research/chitraverse/AMOUNT_AWARE_HOOK_BUDGETS.md) and [exact rational shared-state simulator](research/chitraverse/amount_aware_hooks.py) model multiple constant-product pools, dynamic fee phases, prefunded hook transfers, per-token accounting, and finite menu optimal routing. A common-equilibrium exact wealth identity bounds trader gains by hook spending; an AM-GM surplus bound extends the certificate to initially mispriced pools. The simulator computes a certified rational upper bound using integer square roots. [Twelve regression tests](tests/test_amount_aware_hooks.py) accompany the written proofs; [seven auxiliary Lean lemmas](MathCan/FundedHooks.lean) formalize the accounting skeleton. The nonlinear reserve identity and real AM-GM bound have written proofs and Python checks, with full Lean formalization remaining open.

## CHTR-05: Arbitrary hook settlement and reserve damage (2026-11-10)

[Shared settlement potentials](research/chitraverse/SHARED_SETTLEMENT_POTENTIALS.md) extend the earlier amount-aware model to registered pre/post callbacks that move assets among pools, hook accounts, treasury, sponsors and the trader. The [exact-rational settlement oracle](research/chitraverse/settlement_potentials.py) checks atomic token conservation, explicit transient credit caps, guarded shared phases, custom reserve-product losses, and disjoint/exhaustive accounting roles. It returns a conservative marked-value extraction bound even when the pool invariant decreases. A complete finite state-domain checker validates a local superpotential inequality on every enabled action and refuses incomplete closure. [Twenty-one tests](tests/test_settlement_potentials.py) cover these contracts, including a 108-case exact parameter grid. [Twelve Lean accounting and superpotential lemmas](MathCan/Settlement.lean) establish the abstract path/ledger identities; the nonlinear AM–GM reserve bound has a written proof and rational oracle. This is synthetic mathematics, with no EVM trace equivalence established.

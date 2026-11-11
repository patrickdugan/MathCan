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

## CHTR-06: Integer flash accounting with concrete-trace refinement gates (2026-11-10)

[Trace theorem and scope](research/chitraverse/FLASH_ACCOUNTING_TRACE_REFINEMENT.md), [exact integer replay engine](research/chitraverse/evm_flash_trace.py) and [sample JSON witness](research/chitraverse/fixtures/flash_roundtrip.json) separate PoolManager-style transient obligations from physical token balances, virtual pool allocations, ERC-6909-like redeemable claims and surplus. Nested EVM-like frame reverts roll back all modeled state. Full settlement requires zero signed deltas and nonnegative vault surplus. The replay computes an exact rational extraction receipt with conservative reserve-value floors. [Regression tests](tests/test_evm_flash_trace.py) cover integer fee rounding, taxed transfers, third-party funders, claims, external withdrawals, nested callbacks and observed-balance mismatches. [FlashAccounting.lean](MathCan/FlashAccounting.lean) proves the abstract backing invariant, terminal solvency and a generic finite-trace refinement induction. Actual Uniswap v4 bytecode correspondence, concentrated-liquidity accounting and source-authenticated EVM observations remain explicit proof obligations.

## CHTR-07: Pinned Uniswap v4 transient-state witness (2026-11-11)

[Source-level refinement note](research/chitraverse/POOLMANAGER_SOURCE_REFINEMENT.md) and [exact TSTORE witness checker](research/chitraverse/v4_delta_refinement.py) pin Uniswap `v4-core` commit `bea7f6d1` and model PoolManager's transient per-caller currency deltas, `NonzeroDeltaCount`, lock bit, ERC20/native `sync`/`settle` semantics, hook/caller delta posting, ERC6909 mint and caller-owned burn, and nested reverts. The checker includes pure-Python Ethereum Keccak-256 and validates observed slot/value/order pairs. [Thirty new finite tests](tests/test_v4_delta_refinement.py) include source-specific false-claim and omission examples; [11 finite-support Lean lemmas](MathCan/V4Transient.lean) establish the zero-crossing ghost invariant and lock consequence. **Witness authenticity, concentrated-liquidity execution and pool allocation/value refinement remain open.** Synthetic example: `research/chitraverse/fixtures/v4_delta_roundtrip.json`.
## CHTR-08: Pinned Foundry swap and hook observations (2026-11-11)

[CHTR-08 research note](research/chitraverse/PINNED_FOUNDRY_SWAP_OBSERVATION.md) and [Foundry Solidity probe](research/chitraverse/foundry/MathCanCHTR08.t.sol) execute the **actual** `PoolManager.swap` at pinned Uniswap v4-core commit `bea7f6d1` against a tick-range concentrated-liquidity pool, with permissioned `beforeSwap`/`afterSwap` callbacks and ERC-20 balance settlement. The probe captures transient delta/lock observations via `PoolManager.exttload`, confirms the actual `Swap` event against pool slot0 and active-liquidity readings, and exports a CI observation JSON. An [independent source-limited Python oracle](research/chitraverse/foundry_probe.py), [mutation tests](tests/test_foundry_probe.py) and [seven conditional Lean lemmas](MathCan/FoundryProbe.lean) check the observed accounting. [Pinned Foundry CI](.github/workflows/chtr08-pinned-foundry.yml) archives the forge log and JSON observation. It is still an instrumented test witness, **not** a raw opcode-complete trace or a proof of deployed-bytecode refinement; the observed JSON includes explicit evidence limitations.

## CHTR-09: Ordered PoolManager TSTORE and two-tick Q64.96 refinement (2026-11-11)

[Proof note](research/chitraverse/OPCODE_MULTITICK_REFINEMENT.md), [Foundry test](research/chitraverse/foundry/MathCanCHTR09.t.sol) and [independent source-pinned oracle](research/chitraverse/foundry_opcode.py) instrument the real pinned Uniswap v4-core `PoolManager` with Forge debug-trace recording. They preserve every actual ordered manager `TSTORE` slot/value, match the transaction's transient-state writes against the source-defined zero-crossing and settlement sequence, and check a swap crossing the initialized tick at `-120`, changing active liquidity from `10^18` to `2·10^18`. Exact Q64.96 rounding independently reproduces the two `SwapMath` steps; CI checks compiled deployed bytecode against the observed runtime code hash and archives the source/toolchain provenance. [Nineteen regression tests](tests/test_foundry_opcode.py) reject mutated traces, code hashes, fees, pricing and custody observations. [Eight new Lean lemmas](MathCan/OpcodeRefinement.lean) formalize conditional accounting and refinement statements. The measured source execution is a pinned local Foundry case, with future hook return-delta and fork/deployed-bytecode coverage explicitly open.

## CHTR-10: Permissioned hook deltas and three initialized ticks (2026-11-11)

[CHTR-10 mathematical note](research/chitraverse/HOOK_RETURN_MULTITICK_REFINEMENT.md), [independent integer oracle](research/chitraverse/hook_multitick.py) and [Foundry test](research/chitraverse/foundry/MathCanCHTR10.t.sol) pin Uniswap v4-core at `bea7f6d1` and execute an actual `beforeSwap`/`afterSwap` return-delta hook through `PoolManager`. Four adjacent liquidity ranges cross −120, −240 and −360. The Python checker independently reproduces four exact Q64.96 swap steps, all manager TSTORE operations, the hook/caller split and the funding transfers, with both compiled runtime artifacts bound by code hash. [Twenty-eight new mutation tests](tests/test_hook_multitick.py) pass locally; [Lean lemmas](MathCan/HookMultiTick.lean) prove signed split and finite-path integer identities. The pinned Foundry/Lean CI runs supply runtime/kernel verification separately. The scope is a single instrumented local execution, not all hook bytecode or deployment configurations.

## TOE-01/02: Physics interviews, gauge information and cosmological null tests (2026-11-11)

The [TOE transcript source registry](research/toe/EPISODE_INDEX.json) and [triage](research/toe/TRANSCRIPT_TRIAGE.md) begin a timestamped intake of *Theories of Everything with Curt Jaimungal*, with six episodes including Bianconi, Ravera, Gorard and Verlinde. The [mathematical note](research/toe/GAUGE_ENTROPY_COSMOLOGY.md) derives the Gaussian relative-entropy quotient for graph gauge fields, proves the exact cycle-information and linear coarse-observation inequalities, and constructs a Friedmann polynomial null-space test for synthetic H(z)^2 observations. [Rational oracles](research/toe/graph_entropy.py), [cosmology code](research/toe/frw_null.py), and a [local rights-aware SRT/VTT importer](research/toe/transcript_intake.py) have regression tests. The [Lean graph module](MathCan/TOEGraph.lean) covers elementary gauge/path identities. Noncommutative GQRE, full general relativity and observational claims remain separate scientific proof obligations.

## TOE-03: Bianconi G-field cosmology and covariance-profile tests (2026-11-11)

[Primary-source analysis and four conditional propositions](research/toe/BIANCONI_GFIELD_PROFILE.md) examine the dressed metric equation and G-field-generated cosmological term in Bianconi's 2026 papers. The [exact-rational profiling engine](research/toe/bianconi_profile.py) and [fully disclosed seven-redshift covariance](research/toe/fixtures/bianconi_synthetic_covariance.json) compute a Schur-complement obstruction after eliminating the conventional lambda, curvature, matter and radiation components. A G-field-inspired eigenvalue ansatz has a notable quadratic blind mode `(x²-1)²` that is completely absorbed by these four backgrounds; its cubic term can escape that nuisance span. Fifteen [regression tests](tests/test_toe03_bianconi.py) cover positive-definite covariance, injected signals, systematic calibration invariance and the blind mode. [Lean identities](MathCan/TOECosmology.lean) certify the conditional algebra of background absorption. The expansion history is a **phenomenological proxy**, rather than an integrated solution to the full ΛGfE field equations; every observation in the fixture is synthetic.

## TOE-04: Vacuum ΛGfE FLRW dynamics (2026-11-11)

The [TOE-04 derivation](research/toe/BIANCONI_FLRW_GFIELD_DYNAMICS.md) reconstructs Bianconi's five isotropic G-field curvature eigenvalues, derives the spatially-flat **vacuum** lapse constraint from the logarithmic action with the auxiliary-volume variation retained, and solves a positive-eigenvalue expansion branch in redshift. It includes strict curvature-Hessian convexity, the exact de Sitter limit, a quadratic Gauss–Bonnet cross-check, and an illustrative (high-curvature) trajectory.

[Python solver](research/toe/gfield_flrw.py), [18 tests](tests/test_toe04_gfield.py), [numerical fixture](research/toe/fixtures/gfield_vacuum_synthetic.json), and [nine algebraic Lean lemmas](MathCan/TOEFLRW.lean) accompany the result. The code uses TOE-03's **synthetic** covariance only as an identification test. A fully coupled dressed matter solution, full covariant step proof, and observational H(z) inference remain open. Run `python -m research.toe.gfield_flrw` to print the numerical receipt.

The exact de Sitter branch also passes an independent comparison to Bianconi's covariant Weyl trace equation (45), with a separate regression test. This tests a vacuum fixed point; the evolving covariant residual is still open.

## TOE-05: Bianconi dressed scalar FLRW (2026-11-11)

[Scalar–geometry derivation](research/toe/BIANCONI_DRESSED_SCALAR_FLRW.md), [four-variable solver](research/toe/gfield_scalar_flrw.py), and [synthetic trajectory](research/toe/fixtures/gfield_scalar_synthetic.json) extend TOE-04 to the real homogeneous scalar field in Bianconi's Lambda-GfE induced metric, with the exact matter-dependent scalar/time-vector G-field eigenvalues. The lapse equation and scalar Euler–Lagrange equation form a coupled 2×2 acceleration system. Its Schur determinant is strictly positive for positive alpha, beta, all five induced-metric eigenvalues and expanding H. The determinant decomposition is checked *exactly* in rational arithmetic, and the zero-field limit recovers the TOE-04 vacuum solver. [Twenty new standard-library regression tests](tests/test_toe05_dressed_scalar.py) cover derivatives, continuity exchange, GR normalization, the positive G-field domain and integration convergence. [Lean identities](MathCan/TOEDressedMatter.lean) cover the trace-free FLRW tensor reduction and conditional conservation/positivity logic. These are a symmetry-reduced scalar action and synthetic trajectories; complete covariant dressed stress-tensor and D-tensor refinement remains an open obligation.

## TOE-06: Covariant FLRW gates and strict-principal tensor obstruction (2026-11-11)

[Covariant-audit note](research/toe/TOE06_COVARIANT_AUDIT.md) and the [exact rational tensor-cone / geometric audit](research/toe/covariant_tensors.py) extend TOE-05's dressed scalar FLRW background. The direct four-dimensional FLRW Ricci projection gives the invariant `3*(Hdot-K/a²)²`, and Pereira's symmetry-inheriting strict-principal TT symbol has discriminant `-4*Ws²*(WE-WB)²`. Using the G-field bivector eigenvalues connects these into an exact curvature-proportional discriminant. All six synthetic TOE-05 samples fail that **conditional high-frequency** propagation gate. The independent reduced-action *spatial* Euler–Lagrange residual is checked separately. [23 regression tests](tests/test_toe06_covariant.py), an explicit [synthetic receipt](research/toe/fixtures/gfield_covariant_gates_synthetic.json), and [12 Lean algebraic/cone lemmas](MathCan/TOECovariantGates.lean) accompany the note. The full 4D dressed stress tensor and derivative tensor are still uncomputed, and the executable covariant-source residual interface refuses missing tensor components. A physical viability claim requires a complete 4D component calculation and a cutoff/TT analysis beyond the indicated single-multiplet regime.

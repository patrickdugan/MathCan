# MathCan cross-verse mathematical ledger | 2026-11-10

The source repositories are frozen here to distinguish mathematical derivation from content attribution. These projects include public-source *catalogs* and local-only material, so a source-index entry does not establish a paper's proof content.

| Source project | Pinned revision | Research inputs actually inspected | MathCan development |
| --- | --- | --- | --- |
| [Levinverse](https://github.com/patrickdugan/levinverse/tree/aca03112c722af237940118f22204b4b6ca5dc87) | `aca03112c722` | `README.md`, `research/integration.md`, `research/summaries/uchicago-big-brains-2023.md` | [LVR-01](levinverse/INTERVENTION_QUOTIENTS.md) observation-interface formalism and stochastic error |
| [Chitraverse](https://github.com/patrickdugan/Chitraverse/tree/f89bc19267cf5d7d1ee99af5da4f2293647e34ad) | `f89bc19267cf` | `README.md`, `reports/coverage.md` and linked paper metadata | [CHTR-01](chitraverse/INTERVAL_CYCLE_POTENTIALS.md) rational routing potentials and interval markets |
| [Goodfireverse](https://github.com/patrickdugan/Goodfireverse/tree/b3f8e2932e5b18af591d4970b16ce7ceb4472e63) | `b3f8e2932e5b` | `README.md`, `reports/coverage.md` | [GFR-01](goodfireverse/GRAM_HOLONOMY.md) gauge-loop data and projector invariant |
| [XenobotBench](https://github.com/patrickdugan/XenobotBench/tree/42e7027117ddc67daffc40e83516de67972b54df) | `42e7027117dd` | `docs/MORPHOSPACE_QUOTIENT.md`, `docs/INTERVENTION_CONFLICT.md` | Finite Moore-machine quotient precedent for LVR-01 |
| [RSITopology](https://github.com/MoralityLabAI/RSITopology/tree/4f6f93da08202bc1b81d24d371fe11826d352e4a) | `4f6f93da0820` | `README.md`, `reports/mathematical_program.md`, `research/morphospace_dirichlet/README.md`, `reports/monitor_holonomy_insight.md` reference | Companion operator geometry, autonomy conditions, holonomy motivation |

## Mathematical results added

- **LVR-01/T1–T3:** finite action-relative equivalence, refinement/witness bound and observation/interface monotonicity. T1 is classical Moore-machine partition refinement, already discussed in XenobotBench MOP-01.
- **LVR-01/T4–T6:** under a uniform per-state, per-action quotient-pushforward TV defect ε and macro-history-based policies, complete observed histories are within `1-(1-ε)^T` TV after T steps; the bound is sharp. Rewards in `[0,1]` inherit corresponding expectation bounds.
- **CHTR-02/T1–T7:** exact weighted edge/cycle Hodge energy, a gauge-invariant minimum-energy witness, circulation bounds, global uncertainty margins and sharp unicyclic interval bounds. Six mathematical results and explicit reconstruction; verified by rational finite oracles. Lean formalizes the path gauge algebra, not the weighted matrix identity.
- **CHTR-01/T1–T5:** finite positive exchange-rate graph lacks profitable multiplicative cycles iff positive node potentials exist; synchronous max-product relaxation gives a witness; independent interval uncertainty and concave local conversion have certificates.
- **GFR-01/T1–T5:** two positive-definite Gram matrices realize the same three pairwise projector-overlap magnitudes while giving opposite signed loop holonomy. Full projectors recover the sign via `tr(P0 P1 P2)`. Rank-r invertible overlap polar holonomy is gauge covariant.
- **LEAN-CHECKED candidate:** `MathCan/Intervention.lean` contains six Lean statements for equivalence, action-menu monotonicity, observation postcomposition and action stability. `MathCan/Hodge.lean` adds path concatenation, gauge telescoping, closed path holonomy and residual-gauge cancellation; the new theorems require the current PR CI run.

## Following research slots (conjectures / open tasks)

| ID | Next formal problem | Required verification |
| --- | --- | --- |
| LVR-02 | Quantify minimal control policy regret when a quotient discards action-relevant hidden state and actions are chosen from macro-history | Construct explicit finite counterexamples; prove minimax bound under stated loss |
| LVR-03 | Characterize when action-conditioned predictive-state equivalence remains stable under approximate stochastic quotienting | Separate total-variation bisimulation from weaker endpoint-only equality |
| CHTR-04 | Extend static cycle energy to capacitated networks, concave fills and fixed transaction costs | State correct primal/dual program, then test numerical witnesses |
| CHTR-03 | Analyze adversarial delayed oracle errors and hooks with shared state, beyond rectangular independent intervals | Explicit common uncertainty set and adversary timing |
| GFR-02 | Derive robust perturbation bounds for polar-loop eigenangles when all overlaps have smallest singular value ≥δ | Prove operator-norm stability, track loop length and δ |
| GFR-03 | Test whether triple invariants add held-out identity prediction above pairwise principal-angle summaries on matched synthetic ensembles | Register exact null family before any model measurements |

The mathematical statements describe digital systems and abstract price networks. No physical regenerative ability, market profitability, or model alignment result follows from these modules.

## CHTR-03: State-expanded hook holonomy (2026-11-10)

- **Source motivation:** Chitraverse author/paper catalog, [Chitra et al., optimal routing with hooks](https://arxiv.org/abs/2502.02059), [Uniswap v4 hook lifecycle](https://developers.uniswap.org/docs/protocols/v4/concepts/hooks).
- **Mathematics:** [CHTR-03 note](chitraverse/STATEFUL_HOOK_HOLONOMY.md), eight stated and proved digital results (T1-T8), including a frozen-quote false negative, exact expanded-graph potentials, path-ordered gauge and order defect, a conservative state quotient, and robust interval certificates.
- **Executable evidence:** [exact rational implementation](chitraverse/stateful_hooks.py); [independent tests](../tests/test_stateful_hooks.py) with 625 exhaustive two-state rate assignments, finite-horizon brute force, exact nonlinear constant-product round trips, and explicit gauge/abstraction cases.
- **Lean:** `MathCan/HookState.lean` proves seven auxiliary additive action-word lemmas when the pinned GitHub Lean workflow succeeds; this does not formalize the multiplicative Bellman-Ford converse.
- **Epistemic scope:** synthetic quantity-independent finite-state rates. No deployment arbitrage, real orderbook/AMM, or scientific novelty claim.
- **Next gate:** implement nonlinear amount-aware state transitions, with reserve updates, fee accounting, explicit execution feasibility and finite-horizon reachability verification.

## CHTR-04: amount-aware shared reserves and funded hook budgets (2026-11-10)

- **Source:** [Chitraverse](https://github.com/patrickdugan/Chitraverse) and [Chitra–Kulkarni–Srinivasan 2025](https://arxiv.org/abs/2502.02059); source inspiration only.
- **Mathematics:** [CHTR-04 written proofs](chitraverse/AMOUNT_AWARE_HOOK_BUDGETS.md) of per-pool invariant monotonicity, exact common-equilibrium wealth decomposition, general initial mispricing upper bound using AM-GM, shared-state order dependence, and bounded finite-menu search.
- **Exact executable oracles:** [amount-aware simulator](chitraverse/amount_aware_hooks.py) and [12 standard-library tests](../tests/test_amount_aware_hooks.py), including prefunded hook constraints and 144 equilibrium reserve/fee combinations.
- **Formal scope:** [Lean structural accounting lemmas](../MathCan/FundedHooks.lean) under generic per-action conservation hypotheses; the nonlinear and real square-root lemmas remain written math with rational tests.
- **Risk boundary:** synthetic two-token pools with constant-product fees and prefunded deterministic post-swap hook payments. Token conservation and per-pool nondecreasing product are mandatory. No EVM-accurate callback, external settlement, atomic flash accounting, or real market deployment claim.

## CHTR-05: Shared-settlement extraction certificate (2026-11-10)

- **Source motivation:** Chitraverse's indexed hook-routing literature, especially [Optimal Routing in the Presence of Hooks](https://arxiv.org/abs/2502.02059). This is an independent MathCan derivation for a synthetic digital ledger.
- **Mathematics:** [CHTR-05 proof note](chitraverse/SHARED_SETTLEMENT_POTENTIALS.md) establishes exact complete-ledger funding decomposition, terminal AM–GM reserve-value bounds with arbitrary nonmonotone pool products, rational certified root-floor bounds, and a pathwise superpotential inequality for state-dependent actions.
- **Executable checks:** [registered settlement oracle](chitraverse/settlement_potentials.py) and [21 new Python tests](../tests/test_settlement_potentials.py). All account roles must be exhaustive; each callback is atomically settled with exact rationals. Optional bounded interim overdrafts must be fully cleared at commit. An exhaustive *finite closed-domain* checker validates all enabled action edges and fails closed when its state set misses a reachable state.
- **Lean scope:** [12 abstract accounting/potential lemmas](../MathCan/Settlement.lean), subject to GitHub CI, formalize the structural path inequalities. They assume lower pool-value bounds; the nonlinear AM–GM construction is written mathematics with rational checks.
- **Counterexample:** `pool (100,100) → (90,100)` by transferring `10 A` from reserves to the trader lowers the pool invariant from 10,000 to 9,000. CHTR-04's invariant-growth premise fails; CHTR-05's terminal reserve floor yields an upper bound of approximately 10.263342 on the trader's exact 10-unit gain.
- **Next gate:** port rational AM–GM certificates to Lean, then derive a formal relation between an instrumented EVM/Foundry trace and the registered two-asset ledger, including hook authorization, integer rounding, delta accounting, reentrancy and external sponsor provenance.

## CHTR-06: integer flash-accounting and EVM trace refinement (2026-11-10)

- **Sources:** [Uniswap v4 PoolManager](https://github.com/Uniswap/v4-core/blob/main/src/PoolManager.sol), [flash accounting](https://developers.uniswap.org/docs/protocols/v4/guides/flash-accounting), and [EIP-1153](https://eips.ethereum.org/EIPS/eip-1153); Chitraverse research motivation is distinct from these implementation references.
- **Proved abstract math:** [Flash-accounting T1-T5](chitraverse/FLASH_ACCOUNTING_TRACE_REFINEMENT.md): vault-pool-claim-delta-surplus invariant, per-frame rollback, exact terminal extraction identity, conservative AM-GM bound and conditional multi-step refinement from a verified one-step projection.
- **Executable model:** [Integer interpreter](chitraverse/evm_flash_trace.py), [JSON fixture](chitraverse/fixtures/flash_roundtrip.json), [adversarial tests](../tests/test_evm_flash_trace.py). All transfers have equal-and-opposite entries, with explicit tax recipients. The script rejects unknown assets, unsigned overflows, unsettled deltas, underbacked terminal vaults and failed declared observations.
- **Lean:** [FlashAccounting.lean](../MathCan/FlashAccounting.lean) contains the kernel-level aggregate conservation, terminal inequalities and finite-trace refinement induction, with `#print axioms` checked by the repository workflow. It does not prove equivalence with deployed Solidity.
- **Gate to genuine EVM claim:** authenticated Foundry or RPC trace tied to a verified contract revision, recorded `msg.sender` and revert frame stack, every vault transfer and token balance change, verified claim ownership, and sound abstraction of v4 concentrated-liquidity state. The Python model alone cannot validate the provenance/completeness of caller-supplied events.

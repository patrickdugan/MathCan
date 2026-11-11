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

## CHTR-07: pinned-source PoolManager currency-delta refinement (2026-11-11)

- **Pinned source:** `Uniswap/v4-core@bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6`, specifically `PoolManager.sol`, `CurrencyDelta`, `CurrencyReserves`, `NonzeroDeltaCount` and `Lock`.
- **Mathematics:** [CHTR-07 note](chitraverse/POOLMANAGER_SOURCE_REFINEMENT.md) proves nonzero-count conservation under complete per-account/per-currency delta updates, terminal lock implication, exact ERC20/native settlement distinctions, and rollback of a declared nested trace.
- **Formalization:** [MathCan/V4Transient.lean](../MathCan/V4Transient.lean) encodes the finite-support count/zero-crossing and lock lemmas. These are conditional on a complete concrete step correspondence.
- **Oracle:** [v4_delta_refinement.py](chitraverse/v4_delta_refinement.py) verifies exact Keccak-256 TSTORE delta slots, source-defined static slot constants, int128/int256 arithmetic, per-operation transient write sequences and a finite account supply ledger. [Synthetic fixture](chitraverse/fixtures/v4_delta_roundtrip.json). [30 adversarial tests](../tests/test_v4_delta_refinement.py).
- **Boundary:** The `pool_account` deltas are opaque inputs. No Foundry/Anvil or live EVM trace was authenticated; `complete_source_evidence=false` in every audit. Uniswap's actual concentrated-liquidity pool state has no simple two-token reserve-allocation map. CHTR-06 pool-value conclusions are not yet transported to real v4 transactions.
- **Next gate:** Instrument one pinned `PoolManager.swap` with a hook in Foundry to export omission-complete `TSTORE` writes, internal return deltas, nested rollback, balance snapshots, and bytecode provenance; independently replay and compare against the bridge, then add a checked `Pool.swap` step semantics.
## CHTR-08: actual PoolManager.swap probe (2026-11-11)

- **Source pin:** `Uniswap/v4-core` `bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6`. The pinned Foundry workflow directly checks out the source and recursively pinned submodules before adding one standalone test file.
- **Executable experiment:** [MathCanCHTR08.t.sol](chitraverse/foundry/MathCanCHTR08.t.sol) instruments a real v4-core concentrated-liquidity swap, hook callback, `exttload` currency-delta/lock observations, `Swap` event, pool `slot0` and active liquidity, and physical token settlement.
- **Verification:** [foundry_probe.py](chitraverse/foundry_probe.py) runs independent integer conservation and evidence-shape checks on the actual Foundry-exported observation. Local synthetic mutation tests do not represent Foundry EVM execution.
- **Lean:** [FoundryProbe.lean](../MathCan/FoundryProbe.lean) formalizes seven conditional observations, assuming a complete support list and correct source-observation mapping; kernel success is determined by CI.
- **Additional independent math:** exact integer reconstruction of the observed one-tick `SwapMath`/`SqrtPriceMath` branch: sqrtPriceNextX96 `79228083523865064300074843162`, amountOut `996999005991` for gross token0 input `10^12` and 3000-pip fee. Fails closed on one-unit discrepancies.
- **Remaining:** raw EVM TSTORE/TLOAD trace, compiler build-info/code-hash attestation, arbitrary tick-crossing proof and deployed-hook tests. `complete_source_evidence=false` remains mandatory on the observation report.

## CHTR-09: real opcode evidence and one initialized-tick crossing (2026-11-11)

- **Source:** [`Uniswap/v4-core@bea7f6d1`](https://github.com/Uniswap/v4-core/tree/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6); permissioned hook fixture retained from [CHTR-08](chitraverse/PINNED_FOUNDRY_SWAP_OBSERVATION.md).
- **Theorem notes:** [opcode/tick refinement](chitraverse/OPCODE_MULTITICK_REFINEMENT.md): exact source-defined transient write sequence, independent two-step Q64.96 arithmetic across initialized tick `-120`, and compiled runtime hash correspondence. The finite evidence gates restrict the conclusion to this specific source-pinned Foundry execution.
- **Measured evidence:** [Foundry instrumented test](chitraverse/foundry/MathCanCHTR09.t.sol) uses `vm.startDebugTraceRecording()` to capture actual `TSTORE` opcodes executed by PoolManager. CI checks `PoolManager.json` compiled deployed bytecode and archives submodule SHAs, source pin and toolchain settings.
- **Independent oracle:** [foundry_opcode.py](chitraverse/foundry_opcode.py) reproduces v4 `TickMath` integer multipliers, `SwapMath.computeSwapStep` and `SqrtPriceMath` floor/ceil semantics across two ranges, and matches every ordered manager TSTORE for this deterministic fixture. [Unit tests](../tests/test_foundry_opcode.py) include 19 synthetic mutation cases. No user-provided JSON authenticates its own execution.
- **Lean:** [OpcodeRefinement.lean](../MathCan/OpcodeRefinement.lean) contains eight conditional algebraic/finite-trace lemmas; it does not kernel-verify v4 Solidity, compiler correctness or the Q64.96 arithmetic.
- **Next gate:** nonzero hook-return deltas and multiple-tick routes; eventually source-authenticated EVM trace evidence tied to deployed code hash, external balances, and all relevant callbacks.

## CHTR-10: nonzero hook returns and three crossed initialized ticks (2026-11-11)

- **Pinned source:** `Uniswap/v4-core@bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6`; hook flags `BEFORE_SWAP`, `AFTER_SWAP`, `BEFORE_SWAP_RETURNS_DELTA`, `AFTER_SWAP_RETURNS_DELTA`.
- **Mathematics:** pool/recipient/hook signed-delta partition; four exact-in Q64.96 integer swap steps crossing −120, −240 and −360; total pool output 47,583,989,168,610,240 and final price 77,577,612,008,717,379,644,593,744,931, with terminal tick −422.
- **Empirical gate:** [pinned Foundry harness](chitraverse/foundry/MathCanCHTR10.t.sol) collects the actual PoolManager ordered TSTORE stream, physical transfers, nonzero-delta count, hook balance and Swap event. [Independent oracle](chitraverse/hook_multitick.py) expects 21 manager writes and checks manager and hook compiled bytecode hashes.
- **Tests:** 28 local Python tests covering rounding, source pins, credit, price, hook balance, write omission/reordering and runtime artifact replacement; full MathCan/Foundry CI required.
- **Lean:** [HookMultiTick.lean](../MathCan/HookMultiTick.lean) proves abstract signed-flow and finite-step identities with `#print axioms` checks. The concrete source/event mapping is checked by Foundry and independent Python, not formally reduced to Lean kernel.
- **Research boundary:** test-only permissioned hook, deterministic ERC20 transfers and one pinned local swap. Claims about permissionless or mainnet behavior require independently authenticated bytecode and generalized interface verification.

## TOE-01/02: gauge-relative entropy and cosmological null space (2026-11-11)

- **Sources:** six [TOE transcripts and timestamp anchors](toe/EPISODE_INDEX.json); Bianconi's [gravity from entropy](https://arxiv.org/abs/2408.14391), the [François–Ravera relational framework](https://arxiv.org/abs/2407.04043), and [ΛGfE](https://arxiv.org/abs/2610.34496). Full third-party transcripts stay with their owners or authorized local storage.
- **Mathematics:** [finite Gaussian gauge-quotient and Friedmann null-space proofs](toe/GAUGE_ENTROPY_COSMOLOGY.md); exact-rational graph/cosmology regression tests; explicit identification limits under graph coarsening and redshift sampling.
- **Formal status:** [TOEGraph.lean](../MathCan/TOEGraph.lean) states graph gauge and closed-path lemmas for Lean CI. General positive-definite matrix KL and FRW rank arguments are written proofs, awaiting a Mathlib formalization.
- **Continuation:** review authorized caption sources and primary papers; derive model-specific modified Friedmann equations before observational comparisons; test spectral coarse-graining in RSITopology and Compactification-Theory.

## TOE-03: Bianconi dark-energy observability (2026-11-11)

- **Primary physics:** Ginestra Bianconi, [*Thermodynamics of Gravity from Entropy*](https://arxiv.org/pdf/2510.22545), Eqs. 16, 20, 37 (G-field expression and dressed equation); [*Λ-Gravity from Entropy*](https://arxiv.org/abs/2610.34496), introducing a constant volume Lagrange multiplier in addition to emergent Λ_G. The newer paper appeared after Bianconi's July 2026 TOE interview.
- **MathCan model:** [TOE-03 derivation](toe/BIANCONI_GFIELD_PROFILE.md) profiles an explicitly *assumed* E²(z) mode against the four conventional FRW columns. It derives a Schur-complement determinant formula, exact power-mode degeneracy, and invariance to arbitrary nuisance-aligned calibration covariance. It also finds that the leading quadratic term from the conditional eigenvalue ansatz G_k=1+g_k(x²-1) has shape x⁴−2x²+1, which is null in the four-mode background quotient; higher terms can escape.
- **Executable:** [bianconi_profile.py](toe/bianconi_profile.py) uses exact `Fraction` Gaussian elimination and LDL positivity tests. Its [seven-redshift covariance fixture](toe/fixtures/bianconi_synthetic_covariance.json) records every rational input and result. Fifteen new unit tests include separate Schur determinant calculations, power-mode tests and nuisance-aligned systematic regression checks.
- **Lean:** [TOECosmology.lean](../MathCan/TOECosmology.lean) contains conditional background absorption and normalization lemmas with `#print axioms` (kernel status determined by CI).
- **Boundaries:** synthetic covariance and observations only. The FRW perturbation is phenomenological, not an integration of Bianconi's coupled dressed field equations. The Gaussian profile is a local identification diagnostic, not a cosmological parameter posterior.
- **Next gate:** reduce the full ΛGfE equations for homogeneous/isotropic positive G eigenvalues and matter; integrate their coupled ODEs and attach a versioned observational likelihood with real covariance and experimental window functions.

## TOE-04: vacuum ΛGfE FLRW spectral dynamics (2026-11-11)

- **Sources:** [Bianconi ΛGfE, eqs. (5),(16),(19),(31),(45)–(49)](https://arxiv.org/abs/2610.34496), [Bianconi isotropic spectral decomposition §III.1](https://arxiv.org/abs/2510.22545), and [Pereira quadratic-curvature audit](https://doi.org/10.1103/lxlj-ppwh).
- **Derivation:** [source-anchored mathematical note](toe/BIANCONI_FLRW_GFIELD_DYNAMICS.md) computes five eigenvalues with degeneracies 1,1,3,3,3 and a strictly convex logarithmic vacuum curvature action; lapse variation determines Hddot along an expanding branch. The auxiliary volume constraint is varied before enforcement.
- **Executable:** [flat vacuum ODE and eigenvalue solver](toe/gfield_flrw.py), [18 tests](../tests/test_toe04_gfield.py), [synthetic receipt](toe/fixtures/gfield_vacuum_synthetic.json), and a covariance-only projection using the prior TOE-03 fixture.
- **Formal coverage:** [TOEFLRW.lean](../MathCan/TOEFLRW.lean) proves nine finite algebraic curvature trace identities. The logarithmic variation and ODE remain written/numerical proofs, outside current Lean kernel.
- **Boundary:** No matter-coupled field equations, observed H(z), full covariant step refinement or physical stability determination. Beta H*²=0.02 is a deliberately exaggerated numerical regime.

- **Covariant fixed-point check:** the de Sitter constant-Lambda value from the reduced lapse equals Bianconi's independent equation (45) with D=T=0 within 1e-12 over three couplings; full time-dependent covariant verification remains open.

## TOE-05: Homogeneous scalar matter and full-source trace-free compatibility (2026-11-11)

- **Primary sources:** [Bianconi, Lambda-Gravity from Entropy](https://arxiv.org/abs/2610.34496) Eqs. 5, 7, 9, 16, 19, 31, 45–49; [GfE Thermodynamics](https://arxiv.org/abs/2510.22545) isotropic sector multipliers; [TOE-04](toe/BIANCONI_FLRW_GFIELD_DYNAMICS.md) vacuum baseline. The matter field in this entry is Bianconi's **homogeneous real scalar**, not a generic phenomenological perfect fluid.
- **Exact algebraic reduction:** `Theta_0=1+alpha*m²*phi²-6beta(A+B)`, `Theta_t=1-alpha*pi²-3beta*A` and the three vacuum spatial/bivector factors, all strictly positive. The reduced metric-equation equivalent functional uses `f=-sum multiplicity log Theta` with the volume multiplier varied before its constraint is imposed.
- **Analytical derivations:** scalar Euler–Lagrange equation `d(pi/Theta_t)/dt+3H*pi/Theta_t+m²phi/Theta_0=0`; lapse constraint including `-pi*f_pi`; 2×2 coupled acceleration matrix. For `H,alpha,beta,Theta_i>0`, the Schur determinant has an explicit strictly positive decomposition. The source full covariant trace-free equation gives `X_00+X_spatial=3 kappa (rho_dressed+p_dressed)`, with a **joint** Noether conservation law rather than assumed standalone dressed fluid continuity.
- **Validation:** [exact rational Schur certificate and numerical ODE](toe/gfield_scalar_flrw.py); [20 standard-library tests](../tests/test_toe05_dressed_scalar.py) including 300 rational-domain cases, finite-difference derivative checks, initial-data construction, vacuum regression and RK4 step halving; [synthetic fixture](toe/fixtures/gfield_scalar_synthetic.json).
- **Lean:** [TOEDressedMatter.lean](../MathCan/TOEDressedMatter.lean) proves source trace-free component algebra, vacuum-shift invariance, conditional GR normalization, and generic positive/unique Schur logic. It does not formalize the logarithmic action, positivity of all rational Hessian terms, or the covariant source field equations themselves.
- **Scope / remaining gate:** scalar/metric mini-superspace Euler–Lagrange system with source algebraic G-field constraint. Full metric variation, G-field derivative tensor, dressed `T_mu nu`, Weyl trace relation and perturbative ghost/stability conditions remain unverified for the trajectory. Numerical results are synthetic and are not a fit to observations.

## TOE-06: four-dimensional Ricci projections and tensor-principal audit (2026-11-11)

- **Physics sources:** Bianconi, [ΛGfE](https://arxiv.org/abs/2610.34496), Eqs. (45), (47), (48), and Pereira, [Gravitational Waves and Matter Constraints in Gravity from Entropy](https://arxiv.org/abs/2609.03082), its strict-principal TT cone condition in vacuum, symmetry-inheriting single-multiplet and specified algebraic fluid sectors. Applying the latter to constrained-volume ΛGfE is conditional on the volume multiplier adding no fourth-derivative TT symbol.
- **MathCan derivation:** [TOE-06 note](toe/TOE06_COVARIANT_AUDIT.md), the rational identity `Ricci_TF²=3*(Hdot-K/a²)²`, and the principal discriminant `Δ=-(16/3)*β²*Ws²*WE²*WB²*Ricci_TF²` on the strictly positive G-field branch. The source's scalar sector has no bivector matter response.
- **Computational tests:** [covariant_tensors.py](toe/covariant_tensors.py) plus [23 tests](../tests/test_toe06_covariant.py) evaluate exact inequalities, a normalized Weyl-trace target, and the independent reduced scale-factor Euler–Lagrange residual on TOE-05's six synthetic states. [Receipt](toe/fixtures/gfield_covariant_gates_synthetic.json) marks `full_covariant_tensor_evidence=false`.
- **Lean:** [TOECovariantGates.lean](../MathCan/TOECovariantGates.lean) contains 12 exact integer identities, conditional two-square and null-cone implications. The full tensor quartic, differential equations, effective-field-theory assumptions and original covariant equations remain outside the kernel formalization.
- **Next gates:** derive Bianconi's metric-variation dressed `T_mu nu` and derivative `D_mu nu` independently from her covariant action, verify all FLRW components, then test perturbations and possible two-multiplet escape from Pereira's cone obstruction. Finite-trajectory background consistency alone does not establish a viable cosmology.

## TOE-07: response-cone escape and Ricci derivative completion (2026-11-11)

- **Primary sources:** [Bianconi 2026, ΛGfE](https://arxiv.org/abs/2610.34496) and [Pereira 2026, gravitational-wave/matter obstruction](https://arxiv.org/abs/2609.03082). TOE-05 and TOE-06 supply the inherited synthetic scalar FLRW trajectory and strict-principal tensor polynomial.
- **Results and scope:** [TOE-07 note](toe/TOE07_MULTIPLET_CONE_AND_COVARIANT_COMPLETION.md) establishes the exact effective E/B matching equation `alpha*(mE-mB)=2*beta*(Hdot-K/a²)` and its negative-semidefinite discriminant; constructs nonnegative response values along the inherited synthetic trajectory. This is **algebraic pointwise feasibility**, with no physical multiplet action or coupled matter solution.
- **Restricted no-go:** any number of homogeneous scalar gradients has zero antisymmetric wedge; two individually oriented E-vectors produce an electric response outer-product sum of rank at most two, so they cannot make a nonzero isotropic `c*I3`. This does not rule out richer two-Dirac-Kähler-multiplet structures.
- **Covariant derivative:** [Ricci-response oracle](toe/ricci_response.py) derives `D00=(3/2)*[(U-V)*(Hdot+3H²)+H*(Udot+Vdot)]` and `Ds=-(U-V)*(Hdot+3H²)/2-(Uddot+Vddot)/2-2H*Udot` for a conditional Ricci-response tensor `P^00=-U`, `P^ij=V*g^ij`. The full GfE Riemann/bivector response and dressed matter variation have not yet been calculated; the source-field-equation audit remains open.
- **Executable evidence:** [17 exact-rational tests](../tests/test_toe07_tensor_completion.py), 700 rational Ricci derivative contraction comparisons, 729 two-vector rank instances, [synthetic response fixture](toe/fixtures/toe07_compensation_synthetic.json), and an optional independent SymPy 4D Christoffel derivation. [Lean module](../MathCan/TOETensorCompletion.lean) targets structural signed-response, wedge and Ricci-derivative limit lemmas; kernel status requires GitHub Actions.
- **Independent constraint:** FLRW conformal flatness makes a Weyl-squared addition invisible to the entire background while modifying TT perturbations, so background equations cannot identify the full tensor dynamics without a covariant action. See [Cosmological Higher-Curvature Gravities](https://doi.org/10.1088/1361-6382/ad51c5) for this general point.

## TOE-08: two-form triad action and dynamical cone matching (2026-11-11)

- **Primary sources:** Bianconi [ΛGfE](https://arxiv.org/abs/2610.34496) and Pereira [GW/matter constraints](https://arxiv.org/abs/2609.03082), read for the form-space and high-frequency response problem; they do not supply the specific MathCan action below.
- **New model:** [`TOE08_TWOFORM_TRIAD_ACTION.md`](toe/TOE08_TWOFORM_TRIAD_ACTION.md), with three simple antisymmetric 2-form potentials, kinetic `-H²/12`, mass `-m² B²/4` and curvature coupling `+lambda RBB/4`. The triad restores rotational invariance of the full magnetic response; two simple species have rank <=2. This does not rule out two *complete Dirac–Kähler multiplets*.
- **Written proofs:** curvature response tensor and Riemann symmetries, exact reduced action, lapse/spatial stress, EOM and continuity, E/B mixed-block caveat, power-law matching obstruction, gauge caveat for the massless p=1/2 branch and a separate homogeneous kinetic Hessian.
- **Executable checks:** [`twoform_triad.py`](toe/twoform_triad.py), [`test_toe08_twoform.py`](../tests/test_toe08_twoform.py) with 26 local tests, 1,000 exact continuity samples, random rank tests, a two-form RK4 check, and [`derive_twoform_sympy.py`](toe/derive_twoform_sympy.py) as an optional independent metric variation.
- **Lean:** [`TOETwoFormTriad.lean`](../MathCan/TOETwoFormTriad.lean) contains 10 intended kernel-checked structural lemmas for the finite triad, source block matching and power-law mass obstruction.
- **Unresolved physics:** derive GfE's actual microscopic 2-form `M_(2)`, full four-dimensional dressed stress and nonminimal derivative terms, coupled backreaction, and the entire metric-matter characteristic/symmetrizer; the source-specific constitutive link `m_B=chi*b²` is assumed and separately labeled.

### TOE-08B: two-triad flavor-area dynamics

- **Six antisymmetric potentials:** two independent O(3) magnetic triads with their own mass and nonminimal curvature couplings. This is an explicit MathCan trial matter model, not a source-derived pair of full Dirac–Kähler multiplets.
- **New exact identities:** `S=b1²+b2²`, `Q=b1*v1+b2*v2`, `W=b1*v2-b2*v1`; `Wdot=-3HW+(M1-M2)b1*b2`; `S*(v1²+v2²)=Q²+W²`, and the exact radial identity with positive flavor correction `2W²/S`.
- **Counterexample:** `a=t²`, two massless uncoupled 2-form triads obey the field equations, match `m_B=chi*S` at `t=1`, and differ from the required `S=t⁻²` at `t=2` by exactly `49/9216`; flavor area `W(2)=1/128`. No gravitational backreaction is claimed.
- **Kinetic audit:** exact diagonal homogeneous Hessian degenerates at `lambda1*b1²+lambda2*b2²=M_P²`, with the four-dimensional coupled characteristic and constraint handling still open.
- **Tests:** 14 new Python methods in [`test_toe08_two_multiplet.py`](../tests/test_toe08_two_multiplet.py), including 500 exact radial identities and an analytic counterexample, total 40 new TOE-08 methods.
- **Lean:** additional conditional integer response and flavor-area lemmas in [`TOETwoMultiplet.lean`](../MathCan/TOETwoMultiplet.lean); runtime kernel and axiom audit required.

## TOE-08C: Concrete Yang–Mills triad matter laboratory (2026-11-11)

- **Pinned motivating research:** Bianconi [Λ-GfE](https://arxiv.org/abs/2610.34496); Pereira [GfE gravitational waves and matter constraints](https://arxiv.org/abs/2609.03082); Maleknejad–Sheikh-Jabbari [non-Abelian gauge fields in FLRW](https://arxiv.org/abs/1102.1932). These physical sources motivate the chosen laboratory; the positive observer-frame 2-form Gram map is a MathCan *ansatz* rather than Bianconi's derived matter tensor.
- **Concrete matter action:** two independent minimal SU(2) Yang–Mills multiplets, homogeneous isotropic triads `A_i^a=a psi delta_i^a`, with `E=psi_dot+H psi`, `B=g psi²`, exact `dot E=-2HE-2g²psi³`, stress `rho=3/2 Σ(E²+B²)` and `p=rho/3`.
- **2-form geometry:** full 6×6 Gram matrix `[[mE I,c I],[c I,mB I]]`, determinant `(E1 B2-E2 B1)^6`; exact raw curvature-pair derivative of a **defined optional** `R F F` probe includes a Lorentzian sign reversal of `c`.
- **Dynamic theorem:** in the equal-psi, opposite-E symmetric doublet, `c=0` and `dot c=2g psi (mE-mB)`. Conditional on diagonal matching in flat FLRW, `dot c=4 beta g psi Hdot / alpha`; non-Einstein backgrounds with nonzero gauge amplitude leave the diagonal-response class immediately under the *minimal* YM equations.
- **Backreacted GR demonstration:** rational `beta=1/100`, `alpha=3/50`, `kappa=9/5`, `psi=1/4`, `E1=-E2=1/32`, `H=1`, `Hdot=-9/512`, `Lambda=3045/1024`. Initial diagonal matching and Einstein constraints hold; `c_dot=-3/1024`, while diagonal mismatch has zero first derivative. This is a genuine Einstein–YM initial background, with future one-step integration, rather than a ΛGfE solution.
- **Verification:** [Python implementation](toe/yang_mills_triads.py), [26 regression methods](../tests/test_toe08_yang_mills.py) with seeded exact 6×6 determinants and direct stress contractions, [synthetic receipt](toe/fixtures/yang_mills_two_triad_synthetic.json) and eight [Lean auxiliary lemmas](../MathCan/TOEYangMills.lean) with transitive-axiom audit once CI passes.
- **Open:** replace observer-frame Gram with the correct Dirac–Kähler constitutive embedding and Riemann/Bianchi projection; add the full nonminimal metric and gauge variations; solve the coupled ΛGfE–Yang–Mills background; compute gauge-fixed metric–matter characteristic polynomial including EB mixing, and test strong hyperbolicity and the mode residues.

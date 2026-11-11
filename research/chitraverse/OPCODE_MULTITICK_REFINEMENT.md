# CHTR-09: Ordered opcode evidence and a two-tick concentrated-liquidity refinement

**November 11, 2026.** Source-pinned, concrete Foundry test plus independent integer oracle and Lean lemmas. This extension advances CHTR-08 from in-callback observations to the ordered `TSTORE` instructions executed by the actual PoolManager. It independently reproduces a one-boundary, two-liquidity-range `Pool.swap()` execution using `TickMath`, `SqrtPriceMath`, and `SwapMath` rounding rules.

**Scope.** The tests run a real local EVM with a real compiled Uniswap v4-core `PoolManager`; the hook is a test-only `vm.etch`ed `MockHooks` instance. This is a source-level measurement for one specific execution, with a strict receipt. It is not a proof for all v4 pools, arbitrary hooks, deployments, transactions or MEV executions. It does not make a claim about mainnet bytecode or all storage writes by other contracts.

## Source pin and evidence pipeline

- Upstream: [`Uniswap/v4-core@bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6`](https://github.com/Uniswap/v4-core/tree/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6).
- Foundry test: [`foundry/MathCanCHTR09.t.sol`](foundry/MathCanCHTR09.t.sol). It is copied into `v4-core/test/` along with the CHTR-08 router.
- The compiler and dependencies come from that source revision's `foundry.toml` (Solc `0.8.26`, Cancun, `via_ir = true`, optimizer runs `44444444`) and recursively pinned git submodules. CI captures the configuration and complete submodule SHAs, compiler/toolchain version, and compiled artifact SHA-256.
- Forge's `vm.startDebugTraceRecording`/`stopAndReturnDebugTraceRecording` returns opcode steps, their actual execution contract address and top-of-stack operands. The test filters `opcode = 0x5d` (TSTORE) and `contractAddr = address(manager)`, retaining every manager write in order. An array `manager_tstore_pairs` contains slot, value, slot, value, ... (32-byte words); the step count is also recorded.
- The independent verifier [`foundry_opcode.py`](foundry_opcode.py) checks this exact stream against the pinned `PoolManager` functions, including `Lock`, `CurrencyDelta`, `NonzeroDeltaCount`, and `CurrencyReserves`, with Ethereum Keccak-256 to reconstruct the dynamic slots. It rejects missing, reordered, extra or altered manager writes. Each TSTORE carries *the value before execution* from `DebugStep.stack[0:2]` and is replayed as the resulting persistent transient write. This fixture contains no reverted manager subtree; the checker does not yet reconstruct general nested rollback from opcode traces.
- The verifier reads `out/PoolManager.sol/PoolManager.json` and calculates the Keccak-256 of `deployedBytecode.object`. It requires exact equality with the runtime hash observed by the Solidity test. The single 32-byte NoDelegateCall `original` immutable is filled at the solc-emitted byte offsets using the observed manager address; malformed layouts, unknown additional immutables, unlinked libraries, and hash mismatches fail closed. An upstream source revision and its build settings are also pinned in the CI job. This verifies one locally deployed test instance against its compiled artifact; deployed third-party bytecode requires a separate authenticated chain observation.

## CHTR-09/T1: Source-defined transient write sequence

For the ERC-20 exact-input swap in this fixture, the router begins with zero currency deltas. The manager unlocks, then `swap()` posts a negative currency0 delta and positive currency1 delta. The router `sync()`s the input asset, transfers the exact amount, calls `settle()`, then calls `take()` for the output asset, closing both deltas before relocking.

The expected TSTORE sequence has **13 ordered writes** to manager transient state:

1. `IS_UNLOCKED_SLOT = 1`.
2. `currencyDelta(router,currency0) = -grossIn`, then `NonzeroDeltaCount = 1`.
3. `currencyDelta(router,currency1) = output`, then `NonzeroDeltaCount = 2`.
4. `CURRENCY_SLOT = currency0`, then `RESERVES_OF_SLOT = vault0Before`.
5. `CURRENCY_SLOT = 0` on ERC-20 settlement; `currencyDelta(router,currency0) = 0`, then `NonzeroDeltaCount = 1`.
6. `currencyDelta(router,currency1) = 0`, then `NonzeroDeltaCount = 0`.
7. `IS_UNLOCKED_SLOT = 0`.

**Conditional theorem.** When these are precisely the manager's complete ordered `TSTORE` steps, the zero-crossing count invariant from CHTR-07 shows that the final count of zero entails all involved caller/currency deltas are zero. The fixture also reads these deltas through `exttload` during the callback. The Python oracle checks the exact slot/value sequence and the Solidity test checks both before/after observations. This instrumented transaction is a finite runtime witness for the premises, not a completeness theorem for uninstrumented external calls.

## CHTR-09/T2: Independent two-step Q64.96 arithmetic

The test initializes one `1e18` liquidity position on ticks `[-120, 120)` and an adjacent `2e18` position on `[-240, -120)`. A zero-for-one exact-input swap uses gross amount `10^16` with LP fee `3000` pips (0.3%), starting at price `2^96` and tick 0. The next initialized boundary is tick `-120`. Crossing it changes active liquidity from `1e18` to `2e18`.

Let `Q=2^96`, `P0=Q`, `P1=TickMath.getSqrtPriceAtTick(-120)`, `L1=10^18`, `L2=2·10^18`, `f=3000`, and `F=10^6`. The independent oracle implements the bit-decomposed Q128.128 `TickMath` with the exact source multipliers and rounded Q64.96 conversion. It obtains

```
P1 = 78754240422856966435523493930
```

The first step reaches that boundary. With exact integer round-up for required input and fee,

```
input1 = ceil(L1*Q*(P0-P1)/(P0*P1))
fee1   = ceil(input1*f/(F-f))
spent1  = input1 + fee1
out1   = floor(L1*(P0-P1)/Q)
```

The remaining gross amount `g2 = 10^16 - spent1` is less than the amount needed to reach tick `-240`; it exhausts within the second initialized range. Therefore

```
net2 = floor(g2*(F-f)/F)
P2 = ceil(L2*Q*P1/(L2*Q + net2*P1))
out2 = floor(L2*(P1-P2)/Q)
output = out1 + out2
```

The predicted amounts and price are:

| Measured quantity | Exact independent prediction |
| --- | ---: |
| `input1` | 6,017,734,268,818,166 |
| `fee1` | 18,107,525,382,603 |
| `net2` | 3,952,265,731,181,833 |
| `fee2` | 11,892,474,617,398 |
| `out1` | 5,981,737,760,509,662 |
| `out2` | 3,897,468,468,916,983 |
| `output` | 9,879,206,229,426,645 |
| `P2` | 78,599,845,790,232,178,562,796,990,934 |

The two swap-step equations are the specified specialization of upstream `SwapMath.computeSwapStep` and `SqrtPriceMath`; our Python code is an independent implementation with arbitrary precision integers and exact floor/ceil operations. The output's accuracy for this concrete test is decided in pinned Foundry CI, never inferred from its own synthetic reference fixture.

## CHTR-09/T3: Runtime-to-artifact hash correspondence

The Solidity probe reads the actual `extcodehash` of its deployed `PoolManager`. The Python verification loads the compiled `PoolManager` artifact in the *same pinned checkout* and applies the exact solc `immutableReferences` for the sole `NoDelegateCall.original = address(this)` word, then computes `Keccak256(patched deployedBytecode.object)`. Equality provides a concrete, reproducible runtime-bytecode match under the test's build provenance. The CI artifact captures the full compiler configuration, pinned submodules, toolchain version and artifact SHA-256. Changing any of the tested source revision, runtime, opcode order, fees, tick arithmetic or pool state fails a corresponding verifier assertion.

## Verification

```sh
python -m unittest tests.test_foundry_opcode -v
python -m unittest discover -s tests -v
lake build MathCan
```

The GitHub workflow `.github/workflows/chtr09-opcode-multitick.yml` checks out the upstream commit with submodules, executes the real Foundry test, and runs:

```sh
python3 -m research.chitraverse.foundry_opcode \
  .v4-core/.forge-snapshots/mathcan_chtr09_foundry.json \
  --artifact .v4-core/out/PoolManager.sol/PoolManager.json \
  --out chtr09-verified.json
```

The repository's ordinary Lean CI compiles [`MathCan/OpcodeRefinement.lean`](../../MathCan/OpcodeRefinement.lean) and prints the axioms of eight conditional integer identities and trace-refinement lemmas. The Python arithmetic and bytecode verification are not formalized in Lean.

## Remaining obligations

A broader opcode-level refinement requires coverage of reverted subtrees, all possible hook addresses, dynamic fee changes, protocol fee transfers, exact-output swaps, multiple initialized tick crossings, optional ERC-6909 and native settlement, runtime deployment identities, and all external token semantics. A full concentrated-liquidity accounting proof also requires tick bitmap and per-position fee-growth invariants. The next useful test should introduce *a nonzero hook-return delta* and verify its effect on the caller and hook's distinct transient accounts, then add a genuine mainnet/fork transaction with authenticated bytecode and proof of complete event coverage.

# CHTR-10: Permissioned hook-return deltas across three initialized ticks

**Date:** 2026-11-11. **Source pin:** [`Uniswap/v4-core@bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6`](https://github.com/Uniswap/v4-core/tree/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6).

## Concrete challenge

CHTR-09 matched all 13 `PoolManager` `TSTORE` writes for a fee-only swap traversing one initialized tick. CHTR-10 requires a real test hook with both `BEFORE_SWAP_RETURNS_DELTA_FLAG` and `AFTER_SWAP_RETURNS_DELTA_FLAG`, then a large swap crossing **three** liquidity boundaries. The contract must settle *both* the router's debt and the hook's positive currency claims before relocking.

The test runs the real v4-core `PoolManager`, `Pool.swap`, `SwapMath`, `TickMath`, `SqrtPriceMath`, hook dispatch and EVM transient storage in pinned Foundry. MathCan verifies the observed sequence with independently implemented integer arithmetic and Keccak-derived transient slots.

The test source is [`MathCanCHTR10.t.sol`](foundry/MathCanCHTR10.t.sol); the independent verifier is [`hook_multitick.py`](hook_multitick.py). A GitHub Actions job compiles the pinned repository with its locked submodules and compiler profile, runs the Solidity test, captures exact debug-trace instructions, and rejects observations that differ from the predicted bytecode-dependent evidence.

## 1. The actual hook-return split

For an exact-input, zero-for-one swap with original signed input amount `requested = -50,000,000,000,000,000`, the return-delta hook supplies:

| Hook return | Signed amount, atomic units |
| --- | ---: |
| `beforeSwap` specified | +1,000,000,000,000,000 |
| `beforeSwap` unspecified | +2,000,000,000,000 |
| `afterSwap` unspecified | +3,000,000,000,000 |

The source-defined `Hooks.beforeSwap` computes

\[
A_{\mathrm{pool}} = A_{\mathrm{requested}} + H_{\mathrm{specified}}
=-49,000,000,000,000,000.
\]

`Pool.swap()` computes the **pool** `BalanceDelta`, while `Hooks.afterSwap()` constructs the hook's two-currency delta from the specified and aggregated unspecified returns:

\[
H_0=10^{15},\qquad H_1=5\cdot 10^{12}.
\]

The final caller delta is defined componentwise by

\[
\boxed{\Delta_i^{\rm pool}=\Delta_i^{\rm caller}+\Delta_i^{\rm hook}}.
\]

`PoolManager.swap` credits the hook first and the router second through `_accountPoolBalanceDelta`. Each of the four account/currency pairs becomes nonzero, so the transient counter reaches 4. The hook performs two actual `PoolManager.take` calls to claim its two credits, while the router settles its input and takes its output. The counter returns to zero on successful unlock completion.

These operations correspond to [Hooks.sol](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/libraries/Hooks.sol#L247-L320) and [PoolManager.sol](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/PoolManager.sol#L187-L226).

## 2. Independent four-step exact-input computation

Four adjacent nonoverlapping liquidity bands are initialized using actual `modifyLiquidity` calls. At tick 0 active liquidity is `10^18`. Crossing the initialized ticks −120, −240 and −360 changes active liquidity to `2·10^18`, `3·10^18` and `4·10^18`.

Starting from `P_0=2^96`, the checker independently reproduces `SwapMath.computeSwapStep` with exact integers and a fee of `3,000 / 1,000,000`. It uses the precise rounded `TickMath.getSqrtPriceAtTick(t)` targets and the two rounding directions of `SqrtPriceMath`.

For a target below the current price and liquidity `L`:

\[
A_0^{\rm needed}=\left\lceil\frac{L2^{96}(P-P_t)}{PP_t}\right\rceil,\qquad
F=\left\lceil\frac{3000 A_0^{\rm needed}}{997000}\right\rceil.
\]

If the remaining gross input reaches the target, `A_0^{needed}+F` is consumed and the tick is crossed. In the last partial step, the net input is `floor(remaining·997000/1000000)` and the new price is computed using the source's round-up expression.

The predicted exact intermediate values are:

| Liquidity | Target | Gross input spent | Token1 output |
| ---: | ---: | ---: | ---: |
| `10^18` | −120 | 6,035,841,794,200,769 | 5,981,737,760,509,662 |
| `2·10^18` | −240 | 12,144,327,772,413,790 | 11,891,913,147,748,310 |
| `3·10^18` | −360 | 18,326,113,664,732,406 | 17,731,168,262,741,585 |
| `4·10^18` | partial before −480 | 12,493,716,768,653,035 | 11,979,169,997,610,683 |

Therefore

\[
\begin{aligned}
\Delta_0^{\rm pool}&=-49,000,000,000,000,000,\\
\Delta_1^{\rm pool}&=+47,583,989,168,610,240,\\
\Delta_0^{\rm caller}&=-50,000,000,000,000,000,\\
\Delta_1^{\rm caller}&=+47,578,989,168,610,240,\\
P_f&=77,577,612,008,717,379,644,593,744,931,\\
t_f&=-422,\qquad L_f=4\cdot10^{18}.
\end{aligned}
\]

The tick is established independently by finding the greatest `t` with `TickMath.getSqrtPriceAtTick(t) ≤ P_f`. The final tick is strictly between −480 and −360.

## 3. Complete PoolManager transient write witness

The test uses Forge `vm.startDebugTraceRecording` and `vm.stopAndReturnDebugTraceRecording`, selecting `TSTORE` (`0x5d`) with `contractAddr == PoolManager` and preserving the observed stack order. The independent checker expects **21** writes, with Keccak-256 slots derived from the concrete hook, router and currency addresses.

| Segment | Source-level effects | Expected write count |
| --- | --- | ---: |
| Unlock | lock slot becomes 1 | 1 |
| Post hook and caller deltas | four delta slots with nonzero-counter increments | 8 |
| Hook takes two currencies | two delta slots cleared with counter decrements | 4 |
| Router syncs ERC-20 input | synced currency and balance slots | 2 |
| Router settles input | sync reset, router input delta cleared, counter decremented | 3 |
| Router takes output | output delta cleared, counter decremented | 2 |
| Relock | lock slot becomes 0 | 1 |
| **Total** | | **21** |

The `sync(currency0)` snapshot records **vault custody after the hook takes its
currency0 credit**. In this fixture it equals the pre-swap vault balance minus
`1,000,000,000,000,000`; the earlier balance is stale at the moment of `sync`.
The expected write stream and a regression test bind this intra-unlock timing.

The verifier rejects missing, reordered and modified writes. It checks the final physical ERC-20 movements separately:

\[
\Delta_i^{\rm trader}+\Delta_i^{\rm hook}+\Delta_i^{\rm vault}=0,
\qquad\Delta_i^{\rm vault}=-\Delta_i^{\rm pool}.
\]

`PoolManager` runtime code hash is matched against its compiled artifact with the pinned `NoDelegateCall.original` immutable filled using the actual test deployment address. The permissioned hook's deployed runtime hash is independently matched to its compiler artifact. The test's source pin, Foundry version, submodule SHA set and compiler settings are preserved as GitHub Actions artifacts.

## 4. Lean scope

[`MathCan/HookMultiTick.lean`](../../MathCan/HookMultiTick.lean) proves the additive split identity, finite-path conservation, specified-input adjustment, unspecified-output partition, fee/input aggregation, and observed-support lock consequence. These are small generic integer theorems. The Q64.96 arithmetic and source-level return-delta dispatch are replayed against actual Foundry execution and exact Python rather than formalized in Lean.

## 5. Reproducibility

From MathCan root, run the independent synthetic tests:

```sh
python -m unittest tests.test_hook_multitick -v
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/HookMultiTick.lean
```

The CI workflow [`.github/workflows/chtr10-hook-multitick.yml`](../../.github/workflows/chtr10-hook-multitick.yml) checks out the pinned Uniswap v4-core source and its submodules, copies the test into `.v4-core/test`, runs `forge test`, and evaluates the resulting JSON with both compiled runtime artifacts.

No block explorer, public-chain transaction, deployed hook authorization or universal contract proof is claimed. This one execution covers deterministic ERC-20 inputs, a fee-fixed pool, a locally deployed permissioned hook, three initialized ticks and two positive hook return credits. Token rebases, protocol-fee changes, price oracles, nested hook reentrancy and arbitrary malicious bytecode require separate cases. Pool reserve-value certificates still need an independent model of v4 positions and fee claims.

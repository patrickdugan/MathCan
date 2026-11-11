# CHTR-07: Pinned PoolManager transient-accounting refinement

**2026-11-11.** A source-guided, exact-integer checker for an *ordered declared witness* of Uniswap v4-core's transient accounting. The accompanying Lean proofs concern the finite-support nonzero-delta counter and its lock consequence. Python tests exercise the declared source transitions and adversarial witnesses. **No deployed transaction, onchain bytecode or instrumented Foundry run has been authenticated by this work.** An accepted fixture certifies consistency with the rules below and is not a statement of real-world solvency or exploitable arbitrage.

## Pinned source and scope

`Uniswap/v4-core`, commit [`bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6`](https://github.com/Uniswap/v4-core/tree/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6):

| Source | Relevant operation |
| --- | --- |
| [`PoolManager.sol` L104–114](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/PoolManager.sol#L104-L114) | `unlock` sets transient lock, calls the caller's callback, requires `NonzeroDeltaCount.read()==0`, and locks |
| [`PoolManager.sol` L187–226](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/PoolManager.sol#L187-L226) | `swap` obtains pool and hook deltas, then posts the *hook delta* to the hook and the final *caller delta* to `msg.sender` |
| [`PoolManager.sol` L279–335](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/PoolManager.sol#L279-L335) | ERC-20/native `sync`, `take`, `settle`, `settleFor`, exact positive `clear`, ERC-6909 `mint` and `burn` |
| [`PoolManager.sol` L348–383](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/PoolManager.sol#L348-L383) | Native settlement equals `msg.value`; ERC-20 settlement credits the balance increase from a saved `sync`; `_accountDelta` updates signed deltas and the nonzero count |
| [`CurrencyDelta.sol`](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/libraries/CurrencyDelta.sol) | `TLOAD`/`TSTORE` delta slot is `keccak256(bytes32(uint160(target)) || bytes32(uint160(currency)))`; the stored value is an `int256` encoded as a 256-bit word |
| [`CurrencyReserves.sol`](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/libraries/CurrencyReserves.sol) | ERC-20 sync stores transient currency and balance; native sync resets currency only |
| [`NonzeroDeltaCount.sol`](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/libraries/NonzeroDeltaCount.sol) and [`Lock.sol`](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/libraries/Lock.sol) | Exact named transient slots and zero-crossing/lock writes |

The checker implements **Ethereum Keccak-256**, including independent known-answer vectors, rather than FIPS SHA3-256. It compares exact `TSTORE` sequences, order, slots and values with the steps declared in a witness. Signed delta *increments* must fit `int128`; the resulting cumulative balance must fit `int256`. Native currency is the all-zero address.

## Mathematical statement: nonzero-count refinement

Let \(D(a,c)\in\mathbb Z\) be the transient amount owed *to* account \(a\) for currency \(c\). Let \(N\) be the transient nonzero counter. For one valid `_accountDelta(c, δ, a)`, with \(D'=D(a,c)+δ\), the source program's update is

\[
N'=N+\mathbf 1[D'\ne0]-\mathbf 1[D(a,c)\ne0]. \tag{1}
\]

**CHTR-07/T1 (zero-crossing conservation).** If the initial count is \(N_0=\#\{(a,c):D_0(a,c)\ne0\}\), and every actual delta write and zero-crossing counter update is present in the supplied witness, then (1) preserves that equality along the entire finite transaction. The proof is an induction over a finite support list; `MathCan/V4Transient.lean` formalizes the contextual replacement lemma and count invariant.

**CHTR-07/T2 (lock soundness, conditional).** Given T1 and a complete support enumeration, a successful source-level `unlock` with `N=0` entails \(D(a,c)=0\) for every included pair. The Lean theorem `lock_zero_count` proves the finite-list statement. Merely summing the signed deltas to zero cannot replace counting distinct nonzero account/currency pairs: `+5` and `-5` on different accounts leave `N=2`.

**CHTR-07/T3 (ERC-20 settlement).** If `sync(c)` saved manager balance \(B_0\), the next ERC-20 `settleFor(r)` with no other sync and verified manager balance \(B_1\ge B_0\) credits \(B_1-B_0\) to recipient `r`, not necessarily to `msg.sender`. If a second `sync(c)` occurs after an intervening deposit, it changes the baseline. The checker accepts the resulting uncredited deposit and rejects a fabricated earlier credit. With `sync` reset to native currency, the subsequent unsynced `settle` uses `msg.value` instead. `clear(c,0)` is a source-valid no-op when the current signed delta is zero.

**CHTR-07/T4 (call-frame rollback).** A declared nested revert restores the checkpoint's balances, claim ledger, transient deltas, nonzero count, sync snapshot and lock status. This is an abstract snapshot simulation of transactional rollback; concrete EVM `TSTORE`/`TLOAD` semantics also require authenticating call-depth and caller frames.

## Witness language and tests

Run the self-contained [synthetic witness](fixtures/v4_delta_roundtrip.json):

```sh
python -m research.chitraverse.v4_delta_refinement \
  research/chitraverse/fixtures/v4_delta_roundtrip.json
python -m unittest tests.test_v4_delta_refinement -v
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/V4Transient.lean
```

Every state-changing PoolManager operation supplies an ordered `writes` array of lowercase `(slot,value)` `bytes32` pairs. The checker recalculates the expected sequence using the pinned source grammar. `pool_account` requires the **final hook and caller deltas as independent inputs** and validates their posting order; it does not infer them from the `Swap` event. Its `kind` may be `swap`, `modifyLiquidity`, or `donate`. Hook-level before/after callback calculations and changes to the actual concentrated-liquidity pool state remain independent obligations.

The supplied account map is finite and must enumerate all affected in-scope token holders. `transfer` models ordinary conserving ERC-20 moves; fee-on-transfer tokens require a richer receipt that enumerates the fee collector. This version supports caller-owned ERC-6909 burns; third-party allowance checks and ERC-6909 transfers are outside its grammar. A nested callback may return or revert; an active nested `unlock` fails. The output's `complete_source_evidence` is **always `false`** because a self-declared JSON witness cannot authenticate its own call-stack provenance, contract bytecode, or omission-free event coverage.

## Concrete-to-abstract mapping and open obligations

The bridge from actual EVM execution to this model has a precise desired form. For an authenticated, execution-complete `debug_traceTransaction` or instrumented Foundry trace, recover all PoolManager `TSTORE` writes in original order, contract address, call depth, successful/reverted subtree boundaries, exact external balance changes, and code hash. Decode `(target,currency)` slots with the pinned Keccak rule and reconstruct the typed operations from PoolManager call frames. Under this **step correspondence** the declared event tape must match the source-level writes; the Lean finite-trace refinement theorem from CHTR-06 can then transport abstract properties to the reconstructed execution.

The missing work is operationally concrete:

1. Obtain an authenticated Foundry/Anvil trace from the pinned v4-core revision, with internal delta writes, synchronous snapshots, callback and revert boundaries. Normal transaction logs omit the required per-account transient values and post-hook return deltas.
2. Check deployed or test bytecode against the pinned source and linked-library compilation settings; record chain/fork block and transaction hash where applicable.
3. Independently reconstruct `Pool.swap()` concentrated-liquidity tick arithmetic, protocol fee accrual, liquidity changes, and hook permission/return-delta semantics. The `pool_account` inputs are **opaque** until this is done.
4. Establish a separate backed virtual-allocation interpretation for the CHTR-06 reserve-value certificate. Real v4 `Pool.State` stores `slot0`, liquidity, tick maps, positions and fee growth, **not** the simple `(X,Y)` per-pool reserve map used in earlier MathCan digital models. Its reserve-sum equation is a synthetic accounting hypothesis until reconstructed.
5. Extend observations to fee-on-transfer/rebasing tokens, cross-contract claim transfers, native sends outside payable settlement, and arbitrary reentrancy before broadening the accepted execution language.

**Epistemic labels:** the 11 Lean statements in this module concern generic finite lists and integers and require kernel CI; the Python tests check synthetic microstep evidence against reconstructed source rules. A further security claim about live assets requires authenticated runtime evidence and complete deployed-protocol semantics. Any profit or solvency conclusions remain conditional on that work.

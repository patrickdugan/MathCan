# CHTR-08: Pinned Foundry observations of a real v4-core swap and swap hook

**Status, 2026-11-11:** execution harness, CI job, strict observation oracle, and seven conditional Lean lemmas. Evidence remains conditional on a completed pinned Foundry CI job. The generated JSON is a tested observation of a real `PoolManager.swap` in a Foundry EVM, not a raw opcode-complete trace. It must not be described as authenticated bytecode refinement until the missing gates below are discharged.

## Exact source pin

Source is `Uniswap/v4-core` at [`bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6`](https://github.com/Uniswap/v4-core/tree/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6). The CI workflow checks this commit out directly with recursive submodules, installs Foundry, and copies only the MathCan test source into the upstream project's `test/` folder. The test runs the unmodified `PoolManager` implementation and its actual concentrated-liquidity `Pool.swap`. Foundry uses the pinned upstream `foundry.toml` including Solidity 0.8.26, Cancun EVM and `via_ir=true`.

The test sets up two ERC-20 tokens, initializes a fee-3000 pool at Q64.96 price 1:1, and deposits liquidity in an actual [-120,120] tick range. It etches the upstream `MockHooks` implementation to a test-only address carrying the `BEFORE_SWAP_FLAG | AFTER_SWAP_FLAG` permission bits, which makes both hook callbacks execute. This is an instrumented, simulated hook with zero custom deltas. It does not model a deployed arbitrary hook or live market.

The `MathCanObservedRouter` issues one exact-input zero-for-one swap of `10^12` token atomic units, during which it obtains actual `PoolManager.exttload` observations through Uniswap's `TransientStateLibrary` for the router's currency deltas, `NonzeroDeltaCount`, and lock state. It also obtains `slot0` sqrt price/tick and the active liquidity from `StateLibrary` immediately after `swap`, before settlement. It resolves each negative delta using ERC-20 `sync`, transfer and `settle`, and takes the positive delta, then checks both individual deltas and the global count are zero before `unlock` returns. After the unlock it verifies the lock bit and checks physical trader and manager balances.

The Foundry test independently decodes the actual `PoolManager.Swap` event and confirms its pool ID, caller, two deltas, tick, sqrt price, liquidity and 3000-pip fee match the in-callback observations. The hook's `beforeSwapData` and `afterSwapData` are checked against the nonempty marker passed to `swap`. The active tick stays within the liquidity range, so the liquidity is unchanged while the sqrt price decreases. All token deltas are exact signed integer amounts; rounding is whatever upstream `Pool.swap` actually performed.

## Result identity and finite checks

If the test succeeds, its observation file is `.v4-core/.forge-snapshots/mathcan_chtr08_foundry.json`. The Python checker rejects extra/missing fields and verifies:

- Pinned core revision, distinct onchain test addresses, nonzero runtime code hashes, source fixture schema and fee.
- Zero initial caller deltas and count, two nonzero swap deltas, zero terminal caller deltas and count, and correct unlock/lock transitions.
- Exact equality of `Swap` event amounts, `currencyDelta` results, ERC-20 trader balance changes and opposite manager balance changes for **each currency**.
- Tick/price/liquidity observations and both hook callback markers.

The verifier writes `chtr08-verified.json` with the canonical observation SHA-256 and explicit `complete_source_evidence:false`, `raw_tstore_stream_observed:false`. The source JSON alone can be forged; use the **GitHub CI run and its complete forge log and artifact** for operational provenance. The test-only `vm.etch` hook permits deterministic setup without mining a hook address, and the artifact contains the test runtime hash.

For local reproduction with a Foundry installation and Internet access, checkout the pinned v4-core commit with recursive submodules, copy the test file to `test/MathCanCHTR08.t.sol`, run `mkdir -p .forge-snapshots`, and execute:

```sh
forge test --match-path test/MathCanCHTR08.t.sol -vvvv
python3 -m research.chitraverse.foundry_probe \
  .v4-core/.forge-snapshots/mathcan_chtr08_foundry.json
```

The Python command runs from the MathCan repository root. GitHub Actions performs that workflow in the correct working directories. Standard-library unit tests cover forged/mutated JSON and enforce all observation equalities without installing Foundry locally.

## Exact independent single-tick Q64.96 check

The first pinned Foundry CI execution compiled 121 Solidity files with Solc
0.8.26 and passed the live-in-Foundry swap. Its output gave `sqrtP0 = 2^96`,
`L = 10^18`, exact-input `A = 10^12`, fee `3000 / 10^6`, `tick0 = 0`, and
`tick1 = -1` with no crossing of the initialized [-120,120] position.
The source branch in [SwapMath.computeSwapStep](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/libraries/SwapMath.sol#L51-L86)
uses `FullMath.mulDiv` to floor the input net of fees:

```
net = floor(10^12 * (10^6 - 3000) / 10^6) = 997000000000.
```

The no-tick-crossing, token0-input branch of
[SqrtPriceMath.getNextSqrtPriceFromAmount0RoundingUp](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/libraries/SqrtPriceMath.sol#L31-L52)
then computes, with `Q = 2^96`:

```
nextP = ceil((L*Q*sqrtP0) / (L*Q + net*sqrtP0))
      = ceil((L*Q)/(L + net))
      = 79228083523865064300074843162.
```

[The output amount](https://github.com/Uniswap/v4-core/blob/bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6/src/libraries/SqrtPriceMath.sol#L234-L254)
rounds down:

```
outputB = floor(L*(sqrtP0-nextP) / Q) = 996999005991.
feeA = gross - net = 3000000000.
```

The `foundry_probe.py` verifier now recomputes **both integer values** using
independent arbitrary-precision integer arithmetic and demands exact equality
with the Foundry measurements, the PoolManager `Swap` log, and the token
transfers. A single-unit perturbation to either price or output fails the
verifier. This is a complete independent reconstruction **of the one observed
within-tick math step**, under the stated no-crossing/zero-hook-delta premises.
It leaves multi-tick transitions, cross-tick liquidity changes, protocol fee
branches, customized hook return deltas and generalized execution completeness
for separate work.

GitHub Actions first successful pinned run: [42941287906](https://github.com/patrickdugan/MathCan/actions/runs/42941287906),
Foundry 1.9.0, Solidity compiler 0.8.26. Its CI artifact contains the
instrumented JSON and verbose Forge call trace. CI records a manager runtime
code hash; binary reproducibility attestation is a separate gate.

## Mathematical transfer (conditional)

Write `D0,D1` for the router's two signed currency deltas after swap. In the CHTR-07 finite-support model, `count([D0,D1])=2` whenever both are nonzero. Under a **complete** support enumeration and count correspondence, `N=0` forces all recorded deltas to zero, a theorem already certified in `MathCan/V4Transient.lean`. The seven auxiliary theorems of `MathCan/FoundryProbe.lean` formalize the two-currency specialization, individual ERC-20 conservation, emitted event/caller-balance consistency, and composition of complete per-step zero-sum receipts.

That result validates the observed transaction's token custody: if the manager's and trader's ERC-20 movements sum to zero in each currency, then the pairwise physical totals are unchanged. It does **not** establish a sum of invented `(X,Y)` per-pool reserves. Real `Pool.State` contains slot0, liquidity, tick maps, positions, and fee-growth accumulators. Linking those state variables to a reserve-level value floor, including protocol fees and hook deltas, requires independent mathematics.

## Remaining gates for full source/bytecode refinement

1. **Raw EVM evidence:** record a complete per-call opcode trace with ordered `TLOAD`/`TSTORE`, storage and token calls, raw return data and nested revert boundaries. A `Swap` event and checkpoint views are useful observations but are an incomplete internal execution transcript.
2. **Source-compilation attestation:** save a reproducible compiler build-info artifact and compare deployed runtime code hashes against the expected compiled `PoolManager` and the etched mock-hook implementation. A runtime code hash without build-info attestation is not a code-origin proof.
3. **General tick-step semantics:** the one observed within-tick step now has independent integer reconstruction. Extend it to every `SwapMath.computeSwapStep` and tick crossing, including exact Q64.96 rounding, protocol fees and dynamic hook deltas.
4. **Deployment and external effects:** eventually bind to a block-numbered chain trace, real hook bytecode, fee-on-transfer/rebasing currency effects, and any external accounts. The current Foundry test uses ordinary mock ERC-20s and deterministic zero-delta callbacks.

**Scope:** source-grounded instrumented EVM execution, with each observed equality checked both inside Solidity and in a separate Python oracle. No actual onchain arbitrage, exploited protocol, deployed permission boundary, or universal AMM solvency claim follows from this one finite test.

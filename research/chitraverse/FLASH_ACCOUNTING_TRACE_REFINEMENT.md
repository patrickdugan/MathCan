# CHTR-06: Integer flash accounting, call-frame rollback, and terminal extraction

**Date:** 2026-11-10. **Status:** abstract formal theorem, Lean implementation submitted to kernel CI, standard-library executable model, and adversarial finite tests. A deployed Uniswap v4 hook has **not** been proven to refine this abstract interpreter. The source of an execution trace must be authenticated independently.

## Problem and source boundary

CHTR-05 gave an exact conservation budget for an explicitly complete two-token ledger. Its temporary credit abstraction did not correspond to the EVM's transient currency deltas or ERC-6909 claims. CHTR-06 models those channels separately, including the possibility of nested callback reverts and integer-quantized trade outputs.

This project draws its **operational vocabulary** from Uniswap v4's [flash-accounting guide](https://developers.uniswap.org/docs/protocols/v4/guides/flash-accounting), [PoolManager contract](https://github.com/Uniswap/v4-core/blob/main/src/PoolManager.sol), and [unlock/delta guide](https://developers.uniswap.org/docs/protocols/v4/guides/unlock-callback-and-deltas). The EVM's transactional transient-storage rollback is specified by [EIP-1153](https://eips.ethereum.org/EIPS/eip-1153). The core contract also supports `clear`, `settleFor`, and ERC-6909 claims. MathCan implements a small **Uniswap-inspired model**, rather than a symbolic execution of these Solidity files.

We model two nonrebasing ERC20-like currencies `A,B` with integer atomic units, and a fixed, positive, rational marking vector `(p_A,p_B)`. All token-bearing addresses must be registered in the physical ledger, including the manager, trader, router, sponsors, hook receivers and fee collectors. The manager's pooled token custody is an actual physical balance; per-pool reserves are **virtual allocations** within that custody. A claim denominated in `c` is counted as a redeemable, fully collateralized liability, and is never counted as an ERC20 token held by the beneficiary until redeemed.

Supported opcodes in `evm_flash_trace.py` have explicit integer inputs bounded by signed `int128` where the Uniswap-inspired operation uses such a delta. Aggregate deltas are checked against signed `int256`; physical balances, virtual reserves and claim balances against unsigned `uint256`. The simulator rejects negative physical balances and silent token supply changes. A registered tax transfer must enumerate its collector. Gas and fees payable in unlisted assets are outside the budget.

## 1. The backing invariant

For a single currency `c`, define:

- `B_c`: manager's **physical** ERC20 token balance;
- `R_{i,c}`: virtual amount allocated to pool `i`;
- `Q_{a,c}`: ERC-6909-like redeemable claims held by address `a`;
- `D_{a,c}`: signed transient amount owed *to* address `a` by the manager (a negative number is the caller's debt);
- `S_c`: unallocated manager balance, which can temporarily be negative during an unlock.

Define the exact conservation residual

\[
  I_c = B_c - \sum_i R_{i,c} -\sum_a Q_{a,c}
                  -\sum_a D_{a,c}-S_c.
\]

**CHTR-06/T1 (abstract flash-backing invariant, proved).** If the initial state has `I_c=0`, all admitted abstract steps preserve `I_c=0` for each currency. A successful lock additionally requires `D_{a,c}=0` for every `a,c` and `S_c>=0`, so

\[
  B_c = \sum_iR_{i,c}+\sum_aQ_{a,c}+S_c
       \ge \sum_iR_{i,c}+\sum_aQ_{a,c}. \tag{1}
\]

Proof is an algebraic case split. Each operation produces exactly the paired changes in this table:

| Abstract operation | Custody `B` | Virtual pools `R` | Claims `Q` | Signed deltas `D` | Surplus `S` |
|---|---:|---:|---:|---:|---:|
| Pool delta for caller `q` | 0 | +q | 0 | -q | 0 |
| Physical transfer to manager `q` | +q | 0 | 0 | 0 | +q |
| Physical transfer out of manager `q` | -q | 0 | 0 | 0 | -q |
| Credit observed `settle` deposit `q` | 0 | 0 | 0 | +q | -q |
| `take` physical withdrawal `q` | -q | 0 | 0 | -q | 0 |
| `mint` ERC-6909 claim `q` | 0 | 0 | +q | -q | 0 |
| `burn` ERC-6909 claim `q` | 0 | 0 | -q | +q | 0 |
| `clear` entire positive delta `q` | 0 | 0 | 0 | -q | +q |

The `PoolDelta` quantity can be negative for a hook that releases pool inventory; guards separately require reserves to remain nonnegative. A holder-authorized ERC-6909 claim transfer conserves the aggregate `Q`; a pool-to-pool migration conserves aggregate `R`. Every per-token physical transfer between registered accounts also conserves total physical supply. An amount-aware swap produces two pool deltas of opposite sign in different currencies, where the output is computed by integer division from the reserve snapshot. Induction on the finite event list proves T1.

**CHTR-06/T2 (atomic rollback, proved for the abstract interpreter).** Nested call-frame `revert` restores the entire checkpoint: manager custody, pool allocations, claims, transient deltas, synced currency and surplus. The restored frame therefore satisfies every invariant that held on entry. The outer replay is accepted only if it reaches a final `lock`; all trace failures return the unmodified initial snapshot.

EIP-1153 specifies the relevant transaction-scope rollback behavior for `TSTORE` writes. This model represents it by a complete snapshot; it does not emulate contract-specific transient storage slots, `delegatecall` ownership, or reentrancy guards.

## 2. Integer rounding is included in the theorem

The optional synthetic fee-only CPMM quote uses initial reserves `(X,Y)`, atomic input amount `a>0`, and registered fee fraction `0<f_n<=f_d`:

\[
 b=\left\lfloor\frac{Y f_n a}{X f_d+f_n a}\right\rfloor.
\]

The reserve changes are `X -> X+a`, `Y -> Y-b`, and the caller's delta changes by `-a` in the input currency and `+b` in the output currency. This calculation uses arbitrary-precision Python integers followed by explicit `uint256` / `int128` bounds, and an exact floor. The conservation proof uses the **actual integer** `b`, so there is no error term for an idealized real-valued quote. In this simple fee-only CPMM case, `(X+a)(Y-b)>=XY`. This finite model is distinct from Uniswap v4 concentrated-liquidity tick arithmetic, Q64.96 pricing, protocol fees and configurable hook return deltas.

Transfers involving tax or transfer fees can be checked when both destination and tax collector are explicitly registered, and the vault's actual received amount is credited. `sync(c)` records the manager's current balance, and `settle` credits the signed delta by the net custody increase since that snapshot, consuming the same quantity from `S_c`. A second `settle` without a new sync is rejected **by this restricted ERC20-only interpreter**. In actual Uniswap v4, an unsynced `settle()` uses the native ETH path, where `msg.value` supplies the amount. Overwriting `sync` after an ERC20 deposit changes its crediting baseline, as an adversarial test demonstrates. Native ETH settlement is outside the supported input language.

## 3. Terminal extraction and reserve floors

At lock, signed deltas vanish. Partition terminal claims by beneficiary, and physical balances outside the vault by address. Let `T` denote the trader's **physical ERC20 value plus owned ERC-6909 claims**. Let `O` denote the marked value of every other non-manager physical holder and their claims. Let `P=\sum_i(p_AR_{i,A}+p_BR_{i,B})` and `V(S)=p_AS_A+p_BS_B`.

**CHTR-06/T3 (terminal extraction identity, proved).** Because all listed physical transfers conserve both token totals and (1) holds at both successful endpoints,

\[
  \boxed{\Delta T=-\Delta O-\Delta P-\Delta V(S)}. \tag{2}
\]

All registered sponsor contributions, hook account drawdowns, fee collections, manager surplus consumption, and redemptions of claims are counted exactly once in (2). Physical ERC20 ownership and redeemable claims are separate categories, preventing a double-counted vault asset from turning an accounting credit into spurious wealth.

**CHTR-06/T4 (terminal reserve-curvature certificate, proved).** For each final two-token pool, AM–GM gives

\[
  p_AR_{i,A}+p_BR_{i,B} \ge 2\sqrt{p_Ap_BR_{i,A}R_{i,B}}.
\]

For a positive integer `Q` let `L_Q(z)=isqrt(floor(Q^2 z))/Q`, an exact rational lower bound on `sqrt(z)`. Define `D_O=O_0-O_f`, `D_S=V(S_0)-V(S_f)`. Then

\[
 \boxed{\Delta T\le D_O+D_S+P_0-
  2\sum_i L_Q(p_Ap_BR_{i,A}^fR_{i,B}^f)}.\tag{3}
\]

The verifier checks the *exact gap identity*,

\[
  U_Q-\Delta T =P_f-2\sum_iL_Q(p_Ap_BR_{i,A}^fR_{i,B}^f)\ge0,
\]

using `Fraction` arithmetic. If all pools have nonnegative reserves, the approximation increases the ideal square-root upper bound by less than `2m/Q`, for `m` pools. Endpoint reserve products may have decreased due to custom hook accounting. Consequently, inequality (3) bounds the **reported** extraction without assuming product monotonicity.

## 4. Counterexamples and synthetic test receipts

**Vault depletion detected.** Begin with manager custody and allocated pool reserves both `(100 A,100 B)`. A direct unpaired physical transfer of `10 A` from the manager to a trader conserves total physical supply but creates `S_A=-10`. The final lock rejects the trace as underbacked. A nested callback may reverse the transfer before locking, or a real protocol would revert the entire transaction.

**Funded reserve release.** A hook releases `10 A` from a synthetic pool into its own positive transient delta. Its nested frame then calls `take`, paying `10 A` from the vault to the trader and clearing the hook delta. The final trader gain is `10`, paid by the pool's loss of `10 A`. The reserve-value certificate includes that loss.

**Tokenized claim rather than cash.** The same `10 A` pool release can fund an ERC-6909-like claim minted to the trader. Manager custody stays at `100 A`, virtual pool inventory falls to `90 A`, and `Q_{trader,A}` rises to `10`. The claim is counted once in the trader's terminal wealth, while the manager's backing equality still holds.

**Taxed deposit.** A sponsor sends `10 A`, the manager actually receives `8 A`, and a registered treasury collector receives the other `2 A`. A preceding `sync` followed by `settle` credits only `8 A` to the caller's transient delta. The funding decomposition attributes the entire `10 A` decrease to the sponsor and the `2 A` increase to the treasury.

**Call-frame revert.** A hook opens a nested frame, releases `10 A`, takes it into the trader's wallet, and reverts. The model restores the exact pre-call state and retains no transient credit, pool change or physical transfer. It then locks successfully.

The regression suite also exercises a 54-case small-integer CPMM parameter grid, role-missing failures, incorrect caller names, observed-balance and delta mismatches, repeated settlement, overwritten sync snapshots, token-claim transfers, pool migration, rounding, signed overflow and absent lock.

## 5. Refinement obligations before claiming an EVM proof

**CHTR-06/T5 (conditional trace refinement, Lean-targeted).** Let `C` be a concrete EVM machine, `A` this abstract accounting machine, and `alpha:C->A` a projection of all relevant contract balances, claims, pool states, persistent storage and transient deltas. If every enabled concrete step satisfies

\[
   \alpha(\mathrm{evmStep}(c,o))=
   \mathrm{abstractStep}(\alpha(c),o),
\]

then the equality also holds for every finite sequence of steps, by induction. The Lean module proves precisely this generic induction theorem. Its one-step premise remains **unproven for real contracts**.

A deployable implementation needs independently authenticated, block-pinned call traces; bytecode/code-hash and hook-permission validation; reliable reconstruction of the manager's transient currency deltas; exact observed ERC20 balances at pre/post steps; ERC-6909 liabilities and allowances; a mapping of v4 concentrated liquidity and custom accounting to meaningful pool-floor quantities; token standards and nonstandard callback behavior; and a final-state root or witness proving account completeness. `assert_balance` and `assert_delta` events check declared observations but cannot establish their authenticity by themselves. An RPC call trace is evidence only after its provenance and completeness have been verified.

Further exclusions include native ETH value, gas consumption, `delegatecall` storage ownership, arbitrary external DeFi positions, fee rebases, token mint/burn and unsolicited cross-transaction transfers. Surprising runtime behavior outside this opcode language is a failed refinement obligation, rather than a reason to extend a certificate retrospectively.

## 6. Reproduction

```sh
python -m unittest tests.test_evm_flash_trace -v
python -m unittest discover -s tests -v
python -m research.chitraverse.evm_flash_trace \
    research/chitraverse/fixtures/flash_roundtrip.json \
    --output /tmp/chtr06-roundtrip-receipt.json
lake build MathCan
lake env lean MathCan/FlashAccounting.lean
```

The JSON CLI records a per-event hash chain over accepted abstract steps and the final exact extraction certificate. Output files are create-only. The hash chain authenticates internal ordering **given a trusted input transcript** and provides no independent on-chain attestation.

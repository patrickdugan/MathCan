# CHTR-05: Shared-settlement potentials under adversarial hooks

**Status (2026-11-10):** exact finite-ledger mathematics and standard-library
Python tests. The structural integer accounting and superpotential statements
are submitted as twelve Lean lemmas. The positive-real AM–GM inequality, rational
square-root approximation and nonlinear constant-product swap formula are proved
below and checked by rational arithmetic; their full Lean formalization is open.

## Problem and provenance

CHTR-04 bounded fee-only pool routing with funded hook payments. Its hypothesis
`K_i(t) >= K_i(0)` fails for hooks that remove pool reserves directly, change
pool custody, or run custom accounting. We want an extraction certificate that
survives arbitrary *registered* stateful transfers, including nonmonotone pool
products, sponsor subsidies and a precisely bounded intratransaction credit
facility.

Motivation comes from [Chitraverse](https://github.com/patrickdugan/Chitraverse),
which catalogs [Optimal Routing in the Presence of Hooks: Three Case Studies](https://arxiv.org/abs/2502.02059), and the existing MathCan
[CHTR-03](STATEFUL_HOOK_HOLONOMY.md) and
[CHTR-04](AMOUNT_AWARE_HOOK_BUDGETS.md) models. The statements below are derived
for the **explicit invented two-asset ledger**. Source links identify research
motivation, not attribution of these statements to the papers' authors.

## Model

Let `A,B` be fungible divisible tokens, with positive fixed marking prices
`p_A,p_B`. The finite set of **all** in-scope accounts is partitioned into a
trader `T`, a set of custodian/hook/treasury accounts `H`, external sponsor
accounts `E`, and designated pool accounts `P_1,...,P_m`. An account's holdings
are an exact, nonnegative rational pair `(x_A,x_B)` at each committed state.
Each pool holds nonnegative reserves; a constant-product swap requires strictly
positive reserves at the moment it executes. There is also an unvalued phase
`s` that changes which actions are registered.

A rule specifies its phase guard, pre-swap token transfers, optional ordinary
constant-product swap, post-swap transfers, and next phase. Additional guards
and product floors can be registered. The action is atomic: all changes commit
together or none commit. Exact transfer receipts contain source, destination,
asset, amount, phase and before/after products. Every transfer has *two* ledger
sides, so tokens cannot be issued through an unlisted account.

The program may authorize a **bounded temporary debit** for a specific
account/asset pair inside one atomic rule. The ledger checks the lower balance
after every transfer and demands nonnegative balances before settlement.
This is an abstract finite credit facility, not an EVM implementation of flash
accounting; the receipt reports the maximum transient overdraft. Sponsor
transfers are backed by sponsor holdings and appear explicitly in the budget.
An arbitrary caller cannot create new rules or invent program funding.

## The exact conservation identity

For an account `a`, define fixed-price marked wealth

\[
  V(a)=p_A a_A+p_B a_B.
\]

**CHTR-05/T1 (atomic two-token conservation, proved).** For every successful
registered action, and therefore every finite action word, total holdings of
A and of B across **all** registered accounts are constant.

*Proof.* Every transfer of quantity `q` from account `u` to account `v`
subtracts `q` from the former and adds `q` to the latter, and neither action
changes any other account. A constant-product swap is a pair of transfers,
with its output computed from the current reserves. The phase update transfers
no tokens. Sum per-asset deltas and then induct on the action word. Failed
rules return the original immutable state without committing their local
working dictionary. Temporary debits have equal-and-opposite credits and
must settle before commit. QED.

Let `Delta T = V(T_final)-V(T_initial)`. Define `D_H` and `D_E` as the *positive
when drawn down* aggregate marked-value changes of custodians and sponsors.
Write `V_i^0,V_i^f` for the initial and final marked reserve values.

**CHTR-05/T2 (exact trader funding decomposition, proved):**

\[
\boxed{\Delta T=D_H+D_E+\sum_i(V_i^0-V_i^f).} \tag{1}
\]

This holds regardless of pool products, hook phases, state-dependent fees,
action order, temporary credit and whether a swap occurs. The assumption is
that every involved token account appears exactly once in the role partition.

*Proof.* Multiply the two conserved token totals by the marking prices, add,
and isolate the trader's net change. QED.

The full-role check is a *soundness condition*. Omitting sponsor, custody or
pool accounts from the total permits a fictitious funding-free profit claim.

## Reserve curvature and a rational certificate

Let `K_i^f=X_i^fY_i^f` be each final pool reserve product, and define the
nonnegative true balance slack

\[
S_i^f = p_AX_i^f+p_BY_i^f-2\sqrt{p_Ap_BK_i^f}\ge0.
\]

**CHTR-05/T3 (custom accounting extraction bound, proved).** For any
nonnegative final pool balances and any funded/settled registered route,

\[
\boxed{
  \Delta T\le D_H+D_E+
  \sum_i\left(V_i^0-2\sqrt{p_Ap_BK_i^f}\right).
}\tag{2}
\]

*Proof.* The AM–GM inequality gives
`p_A X+p_B Y >= 2 sqrt(p_A p_B X Y)` for every final pool. Insert this lower
bound for `V_i^f` into (1). QED.

The bound applies when custom hooks **lower** `K_i`. A pool's loss of
reserves then enters the account through its smaller terminal reserve value.
The bound tightens when a hook is forbidden to damage the reserve-product
floor. It is a terminal certificate, with its upper bound computed from the
actual complete final ledger.

For a rational `r>=0`, define a conservative rational square-root floor

\[
L_Q(r)=\frac{\lfloor\sqrt{\lfloor Q^2r\rfloor}\rfloor}{Q}, \qquad Q\in\mathbb N_{>0}.
\]

Integer square roots give `0 <= L_Q(r) <= sqrt(r) < L_Q(r)+1/Q`.
With `l_i=L_Q(p_Ap_BK_i^f)`, form the executable bound

\[
 U_Q = D_H+D_E+\sum_i(V_i^0-2l_i).
\]

**CHTR-05/T4 (exact rational gap identity, proved):**

\[
\boxed{U_Q-\Delta T=\sum_i(V_i^f-2l_i)\ge0.}\tag{3}
\]

The certificate is **entirely rational**; its rounding overhead relative to
(2) is less than `2m/Q`. Given the list of terminal pool holdings, `l_i` and
`U_Q`, a verifier checks the positivity, all total-asset equalities, the role
partition, `l_i^2 <= p_Ap_BK_i^f`, and (3). The Python oracle performs these
checks exactly.

**CHTR-05/T5 (initial reserve slack / invariant damage identity, proved).** Set
`S_i(t) = V_i(t)-2sqrt(p_Ap_B K_i(t))`. The same conservation law yields

\[
\Delta T=D_H+D_E+
 \sum_i\left[
 S_i(0)-S_i(f)+
 2\sqrt{p_Ap_B}\bigl(\sqrt{K_i(0)}-\sqrt{K_i(f)}\bigr)
 \right].\tag{4}
\]

*Proof.* The bracket telescopes to `V_i^0-V_i^f` by the definition of
`S_i`; insert it into (1). QED.

This formula isolates initial reserve-price imbalance, final imbalance and
reserve-product damage in the same budget. If initial pools are at the common
mark equilibrium, `S_i(0)=0`. With nondecreasing products and no sponsor or
custodian drawdown, the trader's gain is nonpositive. Hooks that violate
reserve-product monotonicity must account for the damage term.

## A *prospective* budget under onchain-style invariant commitments

Suppose the protocol verifies `K_i >= k_i^min` at every committed state for
fixed registered values `k_i^min`. Then

\[
\Delta T\le D_H+D_E+\sum_i\left[V_i^0-2\sqrt{p_Ap_B k_i^{min}}\right].\tag{5}
\]

**CHTR-05/T6 (floor-based prospective bound, proved).** The stated bound
follows from (2), monotonicity of square root, and the registered invariant
floor. If terminal custodians and sponsors have nonnegative balances, one
may further replace `D_H+D_E` with their initial marked holdings, giving a
route-independent absolute budget. Both bounds admit rational conservative
floor approximations.

*Proof.* `K_i^f>=k_i^min` implies
`V_i^f>=2sqrt(p_Ap_B K_i^f)>=2sqrt(p_Ap_B k_i^min)`.
Apply (1). Since terminal nonpool holdings are nonnegative, their aggregate
marked drawdown is at most their initial aggregate value. QED.

An ex-ante security claim requires every enabled action to enforce the floors;
checking a particular observed endpoint alone is a replay certificate.

## A general superpotential theorem for arbitrary hooks

For an arbitrary state transition system with registered action set, let
`G(s)` be trader marked wealth, `Phi(s)` any state-dependent risk reserve,
and `c(a,s)` a disclosed authorized external charge. Suppose **every** allowed
transition satisfies

\[
G(F_a(s))-G(s)\le \Phi(s)-\Phi(F_a(s))+c(a,s).\tag{6}
\]

**CHTR-05/T7 (path-superpotential theorem, Lean-targeted).** For any finite
sequence `a_1,...,a_h`, including an adaptively chosen sequence, with resulting
states `s_0,...,s_h`,

\[
G(s_h)-G(s_0)\le \Phi(s_0)-\Phi(s_h)+\sum_{t=0}^{h-1}c(a_{t+1},s_t).\tag{7}
\]

*Proof.* Sum the `h` inequalities in (6). Every interior potential cancels.
If `Phi(s_h)>=0` and the charge sum is at most `C`, then
`G(s_h)-G(s_0)<=Phi(s_0)+C`. A complete-state closed route with nonpositive
charges has nonpositive gain. QED.

The finite-domain `audit_finite_superpotential` independently checks each
enabled edge against (6), demands closure under all enabled transitions, and
produces a concrete violating edge on failure. In a two-phase grant-and-return
fixture, a resource-value potential certifies both transitions, while the
zero potential fails. This auditor is complete only for its explicitly
provided closed state set. The Lean module `MathCan/Settlement.lean` encodes
this theorem, its terminal
bound, and the integer-valued conservation/budget consequences. To obtain a
contract-scale **local** certificate, one must synthesize a potential `Phi`
for all reachable state/phase pairs and check (6) against every enabled hook
rule, including its reserve and oracle effects. A sampled route proves only
its own endpoint certificate.

## Two counterexamples and exact numbers

**CHTR-05/C1: invariant-damaging hook.** Begin with a pool `(100 A,100 B)`,
marking prices `(1,1)`, and zero sponsor/hook balances. A registered hook
transfers `10 A` directly from the pool to the trader. The trader gains `10`,
while the pool's product falls from `10,000` to `9,000`. The old fee-only
`K_f>=K_0` premise fails. Formula (2) yields

\[
\Delta T\le 200-2\sqrt{9000}\approx10.2633403899.
\]

With `Q=1,000,000`, the **exact** rational certificate is

\[
U_Q=\frac{5131671}{500000}=10.263342,\qquad
U_Q-\Delta T=\frac{131671}{500000}.
\]

The program rejects this action if a registered product floor of `10,000`
remains in force. No external donor is present: the pool funds the gain.

**CHTR-05/C2: funded sponsor and flash exposure.** A sponsor with `12 A`
transfers it to a zero-balance trader. The exact certificate reports trader
gain `12`, sponsor drawdown `12`, and zero unaccounted surplus. Another
registered zero-net callback temporarily debits a trader `5 A`, credits the
hook, then repays it. A per-asset credit cap of `5 A` authorizes the excursion;
the final accounts match the initial state and the receipt reports peak debt
`5`. Caps below `5`, or any unreturned terminal debt, abort atomically.

The model also permits fees and pre/post callbacks to depend on a finite phase.
Running two amount-bearing swaps in opposite orders yields distinct reserves
and trader proceeds while maintaining the same global conservation identity.

## Executable verification

```sh
python -m unittest tests.test_settlement_potentials -v
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/Settlement.lean
```

`settlement_potentials.py` retains exact rational states, typed action rules,
registered pre/post transfers, phase guards, optional CPMM swaps and balance
checks. Twenty-one new tests cover reserve drainage, dynamic phases, guards,
credit caps, atomic rollback, prefunded sponsor transfers, dual-source
custody, conservative root rounding, omitted-account detection and a
108-case parameter grid. A finite closed-domain potential auditor checks every
enabled action edge and rejects an incomplete state domain. They are digital unit tests of this declared
model, rather than external proofs of real hook behavior.

## Limitations and next proof obligations

The engine has two divisible fungible assets and a synchronous atomic callback.
It models no real Uniswap v4 source code, hook address authorization, EVM token
integer rounding, concentrated liquidity, fee-on-transfer tokens, reentrancy,
flash accounting across contracts, mutable external oracles, state roots,
priority ordering, deployment, or signed funder receipts. Its transient credit
limit is a synthetic control and must never be described as EVM-compatible.

Before applying these certificates to a deployed protocol, create a
machine-checked step correspondence to an instrumented fork/Foundry trace,
with all pre/post balances, transient deltas, pool-manager locks, custom deltas,
and external transfers included. Formalize the AM–GM reserve floor in Lean
with a suitable ordered-field library, and prove that every concrete
transition preserves the proposed local `Phi` inequality. An oracle-dependent
hook requires a registered price-update adversary and all linked accounts.

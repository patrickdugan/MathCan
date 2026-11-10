# CHTR-04: Shared-reserve and funded-hook budget certificates

**Status (2026-11-10):** mathematical note, exact-rational executable transitions,
finite-horizon search and adversarial synthetic tests. Seven structural accounting
lemmas are submitted for Lean kernel verification. The nonlinear identities and
real-number AM–GM theorem have written proofs and rational tests, with a Lean
formalization still open. There is no deployment, smart-contract exploit claim,
or complete onchain execution model.

## Motivation and source boundary

[Chitraverse](https://github.com/patrickdugan/Chitraverse) catalogs Tarun Chitra,
Kshitij Kulkarni, and Karthik Srinivasan's
[*Optimal Routing in the Presence of Hooks: Three Case Studies*](https://arxiv.org/abs/2502.02059),
which studies routing with limit orders, liquidations/TWAMMs, and noncomposable
hooks. [Uniswap v4 hook documentation](https://developers.uniswap.org/docs/protocols/v4/concepts/hooks)
describes `beforeSwap`, `afterSwap`, dynamic fees and custom accounting; this
Mathematics package implements a deliberately narrower, prefunded account.
CHTR-03 treated constant-multiplier finite-state automata. Real token amounts
and shared pool reserve state now enter each transition. All results below
are independently derived properties of this explicit simplified model and
are not attributed as new discoveries to Chitra or Uniswap.

## Model and atomic transition

There are two fungible assets, A and B, and finitely many ordinary constant-
product pools `i=1,...,m`, each with reserves `(X_i,Y_i)>0`.
A trader and a funded hook account each hold nonnegative amounts of A and B.
An abstract hook phase `s` belongs to a finite set. A registered deterministic
hook program selects, for `(s,i,direction)`, a fee multiplier `0<γ≤1`, a
**post-swap** transfer from the hook account to the trader (a negative transfer
charges the trader), and a successor phase `s'`. Insufficient funds abort the
entire transition. All accounts, reserves, and hook phase are updated atomically.
The trader can pick an eligible pool, direction and exact input amount, or the
amount `all` to consume its entire input-token inventory. It cannot select
arbitrary fee policies or unregistered hook payments. Every swap settles
immediately within the model; the simulator has no borrowing or flash credit.

For an input of `x>0` units of A to a pool `(X,Y)`, the amount of B returned is

\[
y=\frac{Y\gamma x}{X+\gamma x},\qquad
(X',Y')=(X+x,\,Y-y).
\]

The reverse direction exchanges the roles of `X` and `Y`.
Amounts, state transitions and balances are exact `fractions.Fraction` values.
The simulator rejects binary floating-point inputs.

### CHTR-04/T1: fee-only pool invariant growth (proved)

For every successful A-to-B swap,

\[
X'Y'=XY\frac{X+x}{X+\gamma x},\qquad
X'Y'-XY=\frac{XY(1-\gamma)x}{X+\gamma x}\geq 0.
\]

**Proof.** From the output formula `Y'=Y X/(X+γx)`. Multiply by
`X'=X+x` and simplify. The right-hand numerator is nonnegative.
The B-to-A case is symmetric. Thus **each** pool's product stays at least its
initial product under any sequence of permitted fee-only swaps, irrespective
of the shared hook phase and order. Post-swap hook transfers affect the hook
and trader accounts only; they never change reserves directly.

## Exact equilibrium budget decomposition

Fix any positive marking prices `(p_A,p_B)`. Suppose the initial reserve pair
of every pool satisfies the same equilibrium ratio

\[
p_AX_i^0=p_BY_i^0=:v_i>0,
\qquad K_i^0=X_i^0Y_i^0.
\]

After any finite sequence of modeled trades let the final reserves be
`(X_i,Y_i)` and `K_i=X_iY_i`. Define

\[
D_i=v_i\frac{(X_i-X_i^0)^2}{X_i^0 X_i},\qquad
F_i=v_i\frac{K_i-K_i^0}{X_iY_i^0}.
\]

Both are nonnegative by T1. `D_i` is the **reserve displacement gap**, while
`F_i` is an **invariant-growth gap**. Their interpretation follows directly
from the algebra; they are not separately asserted to equal swap fees paid in
a ledger, and neither depends on an assumed infinitesimal linear quotation.

### CHTR-04/T2: exact funded-hook wealth identity (proved)

Let `ΔV_trader` and `ΔV_hook` be final minus initial values at the same fixed
numeraire. Under token conservation,

\[
\boxed{
\Delta V_{\mathrm{trader}}
=-\Delta V_{\mathrm{hook}}-\sum_{i=1}^{m}(D_i+F_i).
}
\]

Consequently, for **any** route length and order,

\[
\Delta V_{\mathrm{trader}}\leq-\Delta V_{\mathrm{hook}}.
\]

If the hook retains nonnegative balances and cannot borrow, the trader's
absolute marked gain is bounded above by the hook's *initial* marked value.
When no value leaves the hook, any positive displacement or invariant-growth
gap forces a strict trader loss relative to the shared equilibrium mark.

**Proof.** Expand the two fractions for one pool:

\[
\begin{aligned}
\frac{(X-X_0)^2}{X_0X}+\frac{XY-X_0Y_0}{XY_0}
&=\left(\frac X{X_0}-2+\frac{X_0}X\right)
 +\left(\frac Y{Y_0}-\frac{X_0}X\right)\\
&=\frac X{X_0}+\frac Y{Y_0}-2.
\end{aligned}
\]

Multiplying by `v=p_AX_0=p_BY_0` shows

\[
D_i+F_i = p_A(X_i-X_i^0)+p_B(Y_i-Y_i^0).
\]

Each trade moves A and B between trader and pools; post-swap callbacks move
assets between hook and trader. Each asset total is constant. Multiply both
asset conservation equations by their positive marking prices, sum over pools,
and rearrange. T1 and positive denominators give the sign. QED.

The exact-rational `baseline_gap(initial,final,prices)` returns all four terms,
checks the identity and rejects mismatched initial equilibrium prices or
missing token conservation.

## Arbitrage budget with initially mismatched pools

The shared-price equilibrium premise matters. When two pools begin with
inconsistent ratios, ordinary cross-market arbitrage can be profitable
**without** receiving any hook subsidy.

Start with pools `(100,200)` and `(200,100)`, a trader holding 20 A and no B,
and both pools charging zero fees. The trader sends 10 A to the first pool,
receiving `200/11` B, then sells all that B into the second pool for `400/13` A.
Its closing balance is `10+400/13 = 530/13` A, so its gain is `270/13` A.
Every token is accounted for, and both reserve products remain unchanged.

A more general *absolute* upper bound on extractable marked value is possible
without shared equilibrium.

### CHTR-04/T3: finite initial mispricing budget (proved)

For arbitrary positive initial pool reserves, nondecreasing reserve products,
funded transfers and positive mark `(p_A,p_B)`, define

\[
S_i=p_AX_i^0+p_BY_i^0-2\sqrt{p_Ap_BK_i^0}\geq0.
\]

Then every finite permitted route obeys

\[
\boxed{
\Delta V_{\mathrm{trader}}
\leq-\Delta V_{\mathrm{hook}}+\sum_i S_i.
}
\]

**Proof.** For each final pool, AM–GM and T1 imply
`p_AX_i+p_BY_i≥2√(p_Ap_BX_iY_i)≥2√(p_Ap_BK_i^0)`.
Therefore its marked value can fall from its initial marked value by at most
`S_i`. Sum these inequalities and apply token conservation as in T2. QED.

For exact rational output, `general_budget` replaces each square root by a
*certified rational lower approximation*: `isqrt(floor(Q²r))/Q` for `r≥0`.
This makes the reported surplus a valid **upper** bound on the exact `S_i`,
within `2/Q` per pool. The implementation uses integer square roots and
integer divisions, with no floating-point optimism. If the radicand is a
rational perfect square whose square-root denominator divides `Q`, the bound
is exact. For the two pools `(100,225)` and `(225,100)` at unit marking prices,
the total initial mispricing budget is **50**, exactly.

## Shared-state order dependence

### CHTR-04/T4: noncomposability with finite amounts (explicit counterexample)

Take two identical-price pools `(100,100)` and `(200,200)`, a trader with
40 A, and a two-phase hook that toggles after every swap. At phase 0 it uses
`γ=1`; phase 1 uses `γ=1/2`. Execute two A-to-B swaps of **10 A each**, one
against each pool. Reversing their order changes which reserve size sees the
larger fee. The two final B amounts differ despite using the same initial
portfolios, identical action sizes and final hook phase.

No outside value enters the system; the T2 budget keeps both final trader
portfolios below their initial marked value. The final pool reserves are
*different*, so this example establishes **noncommutation of full transitions**.
It is not the same-endpoint gauge-invariant order holonomy of CHTR-03/T5.
A stronger geometric curvature result would need to compare routes with the
same final complete market state, including reserves and hook inventories.

## Exact finite-horizon optimization

For a finite declared menu `M` of pool/direction/input-size choices and a fixed
horizon `h`, let `U(s)` be the trader's marked terminal wallet value whenever a
registered terminal condition holds. A finite dynamic program computes

\[
V_0(s)=\begin{cases}U(s)&\text{terminal allowed},\\-\infty&\text{otherwise},\end{cases}
\qquad
V_{k+1}(s)=\max\left(V_0(s),\max_{a\in M:\,a\text{ enabled}}V_k(T_a(s))\right).
\]

### CHTR-04/T5: finite menu optimality (proved by induction)

The recursion returns the greatest terminal marked value among all allowed
routes of length at most `h`. At `h=0` it considers only the empty route. For
`h+1`, every admissible nonempty route begins with one enabled action and has
a suffix of length at most `h`; the induction hypothesis solves the suffix.
The empty route is considered directly. This establishes correctness relative
to the **finite menu and horizon**, with no guarantee of global optimality over
all continuous input amounts. `optimal_route()` caches exact states, permits
`all` input amounts resolved at execution, imposes a state-count cap, and
replays its chosen route before returning.

The tiny positive-control problem automatically recovers the route
A-to-B in the first mispriced pool, then B-to-A in the second, returning with
B inventory exactly zero. This is an executable amount-aware profit, distinct
from a repeating closed-market-state cycle: reserves change after the swaps.

## Verification and limitations

Run from MathCan root:

```sh
python -m unittest tests.test_amount_aware_hooks -v
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/FundedHooks.lean
```

The 12 new tests cover exact token accounting, shared-equilibrium budget
identities, prefunded positive and negative callbacks, two-pool phase-sensitive
order, 144 combinations of fees and reserves for equilibrium conservation,
multiple mismatched-price bounds, certified sqrt floors, finite-horizon search
and invalid/insufficient-funding rejection. The complete suite is run in CI.

`MathCan/FundedHooks.lean` formalizes the **logical accounting skeleton**:
per-action scalar conservation along action words, fixed-price aggregate
conservation from separate asset totals, trader/hook/pool identity, funded
budget inequalities, and the strict-loss corollary. These seven Lean theorems
use integer-valued abstract accounts. The nonlinear formulas T1–T3 are
mathematically derived above and checked using rational Python; they do not
yet have an elaborated real/rational Lean proof. `#print axioms` checks the
Lean portion for admitted or native-reduction axioms.

### Explicit model limits

The model excludes EVM integer truncation, concentrated liquidity, mutable
liquidity positions, external oracle side effects, token transfer taxes,
reentrancy, asynchronous callbacks, shared-pool swaps by competing agents,
flash accounting debt, gas and transaction reverts across contracts. Arbitrary
hooks can use pricing curves other than `xy=k`, mutate reserves, transfer from
accounts outside the marked ledger, or perform non-atomic operations; the
budget certificate requires **both** per-pool product monotonicity and full
token conservation within the listed accounts. It is therefore a mathematical
simulation result, not a universal security claim about real hooks.

**Next research step:** create an abstraction preserving a state-dependent
*upper-value function* despite amount rounding, shared oracle updates, and
hook transfers to parties outside the modeled trading accounts. Build a
separate EVM-accurate fixture and compare each predicted action and balance
delta with a Foundry/Uniswap v4 trace before claiming executable safety.

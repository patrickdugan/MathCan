# CHTR-03: State-expanded exchange potentials, hook-order curvature, and sound quotients

**Status:** finite digital theorem package with exact rational oracles (November 10, 2026). Seven additive path lemmas are provided in Lean for kernel checking (`MathCan/HookState.lean`). The multiplicative finite-graph equivalence, uncertainty rule, and abstraction rule below have mathematical proofs and finite exhaustive checks; they are not asserted to have full Lean formalizations.

## Research question and provenance

Can an exchange network pass every *frozen-market-state* no-arbitrage test while a state-changing sequence of swaps has positive closed-loop gain? If so, what mathematical object certifies consistency when trade order changes subsequent quotes?

The motivating source catalog is [Chitraverse](https://github.com/patrickdugan/Chitraverse). Its list includes Chitra, Kulkarni and Srinivasan, [*Optimal Routing in the Presence of Hooks: Three Case Studies*](https://arxiv.org/abs/2502.02059), which considers limit orders, liquidations/TWAMMs, and noncomposable hooks. Uniswap's [hook architecture](https://developers.uniswap.org/docs/protocols/v4/concepts/hooks) explicitly permits dynamic fees, swap callbacks, and custom pricing. CHTR-01 gives a directed max-product potential theorem; CHTR-02 gives a weighted least-squares Hodge certificate for reversible *additive* quotes. The finite-state framework here is a MathCan extension of these established ideas. No new result below is attributed to Chitra or asserted to be historically novel.

These proofs concern a deliberately limited **finite, deterministic, positive-rate, quantity-independent exchange automaton**. Rates represent multiplicative conversion factors for a standardized abstract transfer. Every enabled route is assumed to compose without slippage, quantity dependence, capacity effects, or changes other than its specified finite-state transition. Real hooks often violate these assumptions; a swap-size or reserve-sensitive model must explicitly include size/inventory/remaining capacity in its state and execution semantics.

## 1. The expanded action graph

Let `A` be a finite nonempty asset set and `S` a finite nonempty market-state set. Each hook `e` has a fixed directed asset pair `u_e -> v_e`, a deterministic transition `T_e:S->S`, and a positive rational multiplier `r_e(s)`. An execution of hook `e` at the expanded node `(u_e,s)` produces `(v_e,T_e(s))` and multiplies the abstract holding by `r_e(s)`.

For a permitted word `w=(e_1,...,e_k)`, the state and asset must advance along its enabled hooks. Its gain is the **path-ordered product**

\[
G_w(s_0)=\prod_{j=1}^k r_{e_j}(s_{j-1}),\qquad s_j=T_{e_j}(s_{j-1}).
\]

Every hook therefore induces `|S|` directed edges of a finite graph `H` whose vertices are `A x S`, including parallel edges and self-loops. A **closed-state route** returns to *both* the initial asset and initial market state. This closure requirement matters: a one-shot asset-return path ending in a different market state has different repeatability semantics.

**CHTR-03/T1 (expanded cycle-potential equivalence).** For finite `H` with strictly positive edge multipliers, the following are equivalent:

1. Every directed closed-state route has gain at most one.
2. There is a strictly positive potential `p(a,s)` satisfying
   \[
   p(v_e,T_e(s))\ \ge\ r_e(s)\,p(u_e,s)
   \]
   for every hook and every market state.

*Proof.* Multiplication of the potential inequalities along a closed route telescopes, leaving `p(start) >= G_w p(start)`, hence `G_w<=1`. Conversely, if every directed cycle has gain `<=1`, any repeated-vertex segment in a walk can be removed without decreasing its product. Thus the maximum gain of all walks terminating at any fixed vertex is attained by a simple path, with an empty path of gain one permitted at each vertex. Let `p(v)` be this maximum. Appending any edge `(u,v)` with rate `r`, then removing repeated-vertex segments, gives `p(v)>=r p(u)`. The finite collection of simple paths yields finite strictly positive maxima. QED.

**CHTR-03/T2 (finite Bellman-Ford certificate).** Initialize every expanded vertex with value 1 and synchronously take max-product relaxations for `N-1` rounds, with `N=|A||S|`. The resulting potentials satisfy every edge inequality precisely when `H` has no profitable directed cycle. Otherwise an edge violates its inequality, and exhaustive simple-cycle extraction can return a closed-state route with gain `>1`.

*Proof.* The `k`th vector holds the best gain among paths with at most `k` edges ending at each vertex. In a network with no profitable cycle, every walk is bounded by a simple path of length `<=N-1`, so the `N-1`st iterate is feasible. Any feasible potential dominates every finite walk via telescoping. If the iterate violates an edge inequality, no globally feasible potential exists, and T1 supplies the cycle. QED.

**CHTR-03/T3 (endpoint growth bound).** Under a feasible potential, any enabled path obeys

\[
G_w\ \le\ \frac{p(a_k,s_k)}{p(a_0,s_0)}.
\]

This follows immediately by multiplying edge inequalities. It holds for open paths as well, with the endpoint ratio measuring the change in the model's pricing numeraire. No profitable *closed-state* cycle means an initially quoted asset can still increase numerically after a **different** final market state.

## 2. A frozen-snapshot counterexample

Consider assets `A,B` and two states `0,1`. Hook `f:A->B` toggles the state and has rates `f(0)=2, f(1)=1/2`; hook `g:B->A` also toggles the state and has rates `g(0)=1/2, g(1)=2`.

In each snapshot, the product `f(s)g(s)=1`; the frozen-state directed graph has a feasible potential. But a *sequential* closed-state route is

\[
(A,0)\overset{f,\times2}{\longrightarrow}(B,1)
\overset{g,\times2}{\longrightarrow}(A,0),\qquad G=4.
\]

Repeating the exact route gives `4^k` in this idealized constant-multiplier automaton, which proves that its expanded graph admits no positive potential. The rates and transitions are synthetic; the construction demonstrates what a frozen-snapshot check omits, with no claim that a physical pool could sustain unlimited growth.

## 3. Gauge transformations and hook-order curvature

Choose any positive function `g:A x S -> Q_{>0}` and transform each edge multiplier by

\[
r'_e(s)=r_e(s)\frac{g(u_e,s)}{g(v_e,T_e(s))}.
\]

**CHTR-03/T4 (gauge telescoping).** Every enabled route satisfies

\[
G'_w=G_w\frac{g(a_0,s_0)}{g(a_k,s_k)}.
\]

*Proof.* Consecutive state/asset factors cancel in the path-ordered product. Thus a closed-state route has exactly the same gain under every gauge. Feasible potentials transform in the corresponding manner, preserving T1's classification. QED.

Suppose two hook words `ab` and `ba` are individually valid from an initial node `x` and have **the same expanded endpoint** `y`. Define the **order defect**

\[
\Omega_{a,b}(x)=\frac{G_{ab}(x)}{G_{ba}(x)}.
\]

When both are same-asset loops, `Omega = a(s)b(T_a(s))/(b(s)a(T_b(s)))`. The equality of terminal states holds, for example, if `T_a T_b = T_b T_a` at the starting state; global commutativity is unnecessary.

**CHTR-03/T5 (gauge-invariant order defect).** Under the common-endpoint condition, `Omega` is independent of the choice of positive node gauge.

*Proof.* Both gains receive the same factor `g(x)/g(y)` from T4. Their ratio is therefore unchanged. If endpoints differ, the residual factor `g(y_ba)/g(y_ab)` generally changes the ratio, so a purported gauge-invariant commutator would be ill-defined. QED.

Example with a single asset and two states: hook `a` toggles the state with rate `1/2` in both states; hook `b` leaves the state fixed and has rates `3/4` at state 0 and `1/4` at state 1. From state 0, `G_ab=1/8`, `G_ba=3/8`, giving `Omega=1/3`. Both orders lose value; their unequal gains measure **order curvature**, which by itself need not be a profitable cycle. If an admissible reverse path exists with reciprocally priced execution, a difference between same-endpoint routes can create a profitable closed itinerary. That extra execution assumption must be checked separately.

## 4. Sound state abstraction

For a state partition `alpha:S->Q`, suppose each hook respects it:

\[
\alpha(T_e(s))=\tau_e(\alpha(s))\quad\text{for every }s.
\]

Define the upper rate in abstract state `q` as `U_e(q)=max_{s:alpha(s)=q} r_e(s)`.

**CHTR-03/T6 (sound conservative quotient).** If the abstract expanded graph on `A x Q`, with transition `tau_e` and rates `U_e`, has a feasible potential `P(a,q)`, then `p(a,s)=P(a,alpha(s))` is feasible for the exact graph. Every concrete closed-state route therefore has gain `<=1`.

*Proof.* For each concrete transition, use `r_e(s)<=U_e(alpha(s))`, apply abstract potential feasibility, and substitute `alpha(T_e(s))=tau_e(alpha(s))`. QED.

The implication is one-way. For example, let `f:A->B` and `g:B->A` toggle two states, with `f(0)=2`, `f(1)=1/2`, `g(0)=2`, and `g(1)=1/4`. Its two classes of closed-state two-step products are `2*(1/4)=1/2` and `(1/2)*2=1`; all concrete closed-state cycles have gain `<=1`. Collapse both states to one abstract state: upper rates become `U_f=U_g=2`, giving a **spurious** abstract product 4. Thus failure to find an abstract upper potential is an inconclusive screening result.

A partition whose states have different *abstract successor classes* for the same hook fails the determinism condition. Such partitions must be refined or represented by nondeterministic abstract transitions, with the corresponding conservative constraints.

## 5. Bounds under uncertain quotes

Let the hook transitions be known exactly, while each rate lies in a declared interval `0<l_e(s)<=r_e(s)<=u_e(s)`. The uncertainty may be correlated across edge/state pairs; assume only the componentwise bounds.

**CHTR-03/T7 (robust certificates).** A feasible expanded potential for **all upper rates** certifies the absence of profitable closed-state cycles for every allowed assignment. Conversely, a closed-state cycle with **product of lower rates greater than one** is profitable under every allowed assignment.

*Proof.* Every cycle's gain is monotone in each of its positive edge multipliers, counting repeated appearances. A potential valid at the upper rates is valid at every smaller rate. A lower-rate profitable closed itinerary keeps the same deterministic state transitions and has at least its lower product under every realization. QED.

If upper rates are simultaneously attainable as one permitted rate assignment, upper-rate feasibility is also **necessary** for robust absence of profitable cycles. With correlated admissible rates, the upper-rate test is a conservative sufficient condition. Uncertain transitions, quantity-dependent rates, and interdependent execution failures are outside T7.

## 6. A boundary with the earlier Hodge theorem

CHTR-02's weighted Hodge energy uses the underlying graph viewed with reversible additive quotes. Its nonzero least-squares cycle residual is an obstruction to a pure potential *equality*. CHTR-03's directed inequality potential is an obstruction to positive **directed** cycles.

For a concrete separating example, take the directed acyclic graph `A->B`, `B->C`, `A->C` with all multipliers 2. Directed no-profitable-cycle is automatic because the graph is acyclic, and a feasible positive potential exists. But assign additive quotes `(1,1,1)` to those edges; the undirected triangle has circulation `1+1-1=1`, with unit-weight Hodge least-squares energy `1/3`. Thus nonzero geometric holonomy and profitable executable cycles are different predicates unless the allowed reverse operations are modeled.

## 7. Verification, epistemic status, and extensions

Run `python -m unittest tests.test_stateful_hooks -v` for exact `Fraction` calculations. The ten new regression tests include a 625-network exhaustive grid comparing max-product Bellman-Ford with an independently implemented simple-cycle oracle, a 100-seed finite-horizon brute-force comparison, all corners of a four-parameter rate box, and gauge, quotient, and validation checks. These tests verify the finite implementation and stated fixtures; the proofs above supply the general finite statements.

`MathCan/HookState.lean` states and proves the additive action-word concatenation, gauge telescoping, bounded path sums, closed-loop exclusion under a feasible potential, and gauge invariance of the order defect in an integer additive model. The Lean lemmas are narrower than the full multiplicative price-potential theorem and rely on ordinary integer arithmetic.

**Next research problem (open):** construct a sound abstraction for genuine nonlinear, size-dependent, noncomposable hooks, in which the market state includes reserves, remaining hook budget, and settlement status. Seek a computable upper-value function with certified approximation error and distinguish a finite executable profit from repeatable closed-state arbitrage. Contract-level semantics, gas, balance rounding and external oracle responses must enter the model before an onchain security claim is justified.

## 8. Nonlinear finite-swap comparator: a single constant-product pool

The state-expanded multiplier example assumes that all quantity-independent rates remain available exactly as quoted. For a constant-product market maker, trade sizes change the reserve state, so the simulator must track reserves and outputs together. This yields a useful, independently checkable boundary theorem.

Let a fee-only pool hold reserves `X>0` units of A and `Y>0` units of B. An A-input trade of size `x>0` with fee multiplier `0<gamma<=1` receives B output

\[
y=\frac{Y\gamma x}{X+\gamma x},\qquad
(X',Y')=(X+x,\,Y-y).
\]

An independent hook state may determine the `gamma` for each direction and change after each swap; require only that every realized multiplier remains in `(0,1]` and that its hook adds no separate balance deltas or reserve mutations.

**CHTR-03/T8 (nonlinear two-leg fee-only no-profit theorem).** Execute A-to-B with fee multiplier `gamma`, then immediately B-to-A using *all* received B output and multiplier `beta`, both at their sequentially updated reserves. The recovered A amount `x_back` satisfies `x_back<=x`, with equality if `gamma=beta=1`. The product of the pool's reserves cannot decrease across either swap.

*Proof.* The first pool update changes its product as follows:

\[
X'Y'=(X+x)\frac{XY}{X+\gamma x}
 =XY\frac{X+x}{X+\gamma x}\ \ge\ XY.
\]

For the B-to-A trade, output increases monotonically with its effective fee multiplier. Thus the back-swap output for `beta<=1` is bounded by its `beta=1` output. At `beta=1`, observe `Y'+y=Y` and compute

\[
x_{\text{back}}
\le\frac{(X+x)y}{Y}
=\frac{(X+x)\gamma x}{X+\gamma x}
\le x,
\]

since `gamma X <= X`. The reverse swap's reserve product also cannot decrease by the same argument with the reserve roles interchanged. When both fee multipliers equal one, every inequality is an equality. QED.

`nonlinear_pool.py` implements these steps with `Fraction` and rejects fees outside `(0,1]`. The test enumerates 162 combinations of starting reserves, amount, and dynamic two-leg fees, checking recovery, hook state changes and reserve-product monotonicity. This proves that the synthetic gain-four automaton cannot be realized by **one ordinary fee-only constant-product pool** with the stated reserve accounting. Richer hooks can alter exchange accounting, and networks of several pools can exhibit ordinary cross-market arbitrage; those systems require their own state transition contracts.

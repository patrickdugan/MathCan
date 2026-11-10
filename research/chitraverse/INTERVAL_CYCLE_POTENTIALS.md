# CHTR-01: Multiplicative cycle potentials and interval-rate certificates

**Status:** Exact finite network mathematics with constructive proofs and rational arithmetic tests (2026-11-10). The results concern a simplified abstract exchange graph, not a claim about executable profit in real markets.

**Research bridge:** [Chitraverse](https://github.com/patrickdugan/Chitraverse/blob/f89bc19267cf5d7d1ee99af5da4f2293647e34ad/reports/coverage.md) catalogs Tarun Chitra's work on [constant-function market-maker price oracles](https://arxiv.org/abs/2003.10001), [MEV under uncertainty](https://arxiv.org/abs/2309.14201), and [optimal routing with hooks](https://arxiv.org/abs/2502.02059). Those links identify motivating research topics. The certificates below are a MathCan derivation of standard multiplicative difference-constraint facts; they are not attributed to Chitra or claimed as novel priority.

## 1. The finite marginal-conversion graph

Let `V` be finite. Every directed edge `e=(u,v)` has a positive net marginal exchange rate `r_e>0` in units of asset `v` per unit of asset `u`, with fees already reflected in that rate. An infinitesimal walk multiplies its edge rates. A directed cycle `C` is *profitable at the marginal model* when `R(C)=∏_{e∈C} r_e>1`.

**CHTR-01/T1 (cycle–potential equivalence).** The following are equivalent:

1. Every directed cycle has product at most one.
2. There are strictly positive node potentials `p_v` with `p_v ≥ r_(u,v) p_u` for every edge.

One potential may be constructed as the maximum product of all simple directed paths ending at `v`, including the empty path at each vertex, whose product is one.

*Proof.* Multiplying `p_v ≥ r_e p_u` around a directed cycle gives `p_start ≥ R(C)p_start`, hence `R(C)≤1`. Conversely, suppose every cycle has product at most one. Removing any repeated-vertex segment from a directed walk deletes a cycle of product at most one and weakly increases the product of the remaining walk. Every walk therefore has product bounded by a simple path with the same endpoint. Since the graph is finite, the maximum over all source-to-`v` simple paths exists and is positive. Appending an edge to a maximizing walk to `u`, then deleting repeated-vertex cycles, gives a walk to `v` with product at least `r_(u,v)p_u`. Maximality of `p_v` proves the inequality.

**CHTR-01/T2 (constructive finite decision).** Starting with `p_v^(0)=1`, iterate synchronously

\[
p_v^{(k+1)}=\max\Bigl\{p_v^{(k)},\ \max_{(u,v)\in E}r_{uv}p_u^{(k)}\Bigr\}.
\]

If after `|V|-1` rounds every edge inequality holds, these values certify marginal cycle non-profitability. If an inequality fails, a profitable directed cycle exists. This is the max-product version of Bellman–Ford.

*Proof.* By induction, the `k`th vector contains the maximum product of walks ending at each vertex with at most `k` edges, allowing an empty starting walk. If all cycles have product at most one, every walk reduces to a simple path of at most `|V|-1` edges without losing product; hence round `|V|-1` yields a feasible potential by T1. If an edge inequality fails, no feasible potential can exist at this iterate, and T1's contrapositive proves the existence of a profitable cycle.

No logarithm rounding is needed when rates are rational. The Python certificate retains exact `Fraction` values.

## 2. Uncertainty intervals

For each edge, suppose the realized marginal rate independently satisfies `0<l_e≤r_e≤u_e`.

**CHTR-01/T3 (robust upper-rate certificate).** Every allowed assignment of rates is free of profitable directed cycles **if and only if** the all-upper-rate graph has no profitable cycle. The corresponding upper-rate potential is a simultaneous witness:

\[
p_v\ge u_e p_u\ge r_e p_u\quad\text{for all edges and allowed rates.}
\]

*Proof.* Monotonicity of products shows every realized cycle product is at most its upper-rate counterpart. The all-upper assignment itself belongs to the independent rectangular uncertainty set, giving the converse.

If edge uncertainties are correlated, the same upper-rate potential remains a **sufficient** certificate; the reverse implication can fail when upper rates cannot occur simultaneously.

**CHTR-01/T4 (guaranteed-cycle certificate).** If some directed cycle satisfies `∏_{e∈C}l_e>1`, that *same cycle* is profitable for every allowed rate assignment. When the lower-rate network has no profitable cycle but the upper-rate network does, the interval-only answer is unresolved; one permissible assignment may support a profitable cycle while another does not.

The certificate categories in the accompanying program are `robust_no_cycle`, `guaranteed_cycle`, and `unresolved`. They refer only to these mathematical rate intervals.

## 3. Connecting marginal rates to nonlinear conversion curves

For each edge let `f_e:[0,δ_e)→[0,∞)` be a nondecreasing concave conversion rule near zero, with `f_e(0)=0` and right derivative `r_e=f'_e(0)>0`. Assume the cycle's sequential conversions remain in their domains for sufficiently small input.

**CHTR-01/T5 (local nonlinear cycle criterion).** For any fixed directed cycle `C`:

- If `R(C)≤1`, its composition satisfies `f_C(x)≤x` whenever every leg is within the domain of the stated concave rules.
- If `R(C)>1`, then `f_C(x)>x` for all sufficiently small positive `x`.

*Proof.* By concavity, the supporting tangent at zero bounds each leg: `f_e(x)≤r_e x`. Repeated substitution gives `f_C(x)≤R(C)x`. For the second assertion, the chain rule for right derivatives at zero gives `f'_C(0)=R(C)>1`, since each leg starts at zero and has positive derivative. Thus `(f_C(x)-x)/x→R(C)-1>0` as `x↓0`.

This theorem concerns a *single pure cycle*. Concurrent orders, inventory constraints, state-dependent quotes, latency, fixed transaction costs, hook callbacks, rounding, capacity, and reserve feedback across visits require separate models. Positive marginal gain alone need not produce economically executable profit.

## 4. Exact checks and further conjectures

The executable oracle uses `Fraction` and tests all **4,096** directed-rate/absence configurations on the six nonloop edges of a three-vertex graph, checking agreement between potential feasibility and exhaustive simple-cycle search. It also tests interval certificates, positive self-loops, and the concave conversion family `f(x)=r x/(1+kx)` with `k≥0`.

Suggested follow-on questions, **unproved and not included in T1–T5**, are: a robust potential under joint hook-state uncertainty; certificates for bounded trade sizes and nonlinear order interactions; and minimax routing with correlated oracle errors. Each will need an explicit adversary and timing model.

Run from the repository root:

```sh
python -m unittest tests.test_chitraverse -v
```

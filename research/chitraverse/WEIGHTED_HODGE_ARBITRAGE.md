# CHTR-02: Exact cycle-energy certificates and robust exchange holonomy

**Status (2026-11-10):** Six proved finite-dimensional propositions, a seventh explicit reconstruction result, seven `Fraction`-based regression tests and a small Lean path-holonomy module. All weighted minimization results have mathematical proofs here; the Lean code currently formalizes the additive gauge algebra, not the weighted minimization theorem. Novelty is claimed for neither Hodge decomposition nor its application to graph-based exchange-rate consistency.

**Source trail.** MathCan's [CHTR-01](INTERVAL_CYCLE_POTENTIALS.md) proves the directed multiplicative cycle/potential criterion. Chitraverse records Tarun Chitra's work with Angeris, Evans and Boyd on [CFMM routing](https://arxiv.org/abs/2204.05238) and with Kulkarni and Srinivasan on [routing with hooks](https://arxiv.org/abs/2502.02059). The algebra here uses the classical graph gradient/cycle decomposition, as discussed in [Columbia's incidence/cycle-space notes](https://www.cs.columbia.edu/~djhsu/CLA/notes/connectivity.pdf) and [Hoppe and Schaub (2024)](https://proceedings.mlr.press/v231/hoppe24a.html). These are motivating connections and antecedents, not claims about implementation, economic executability or authorship.

## Model: a reversible additive quotation system

Let a **connected** undirected multigraph have `n≥1` vertices and `m` edges. Select an arbitrary orientation for each edge `e=(u,v)`. A real additive quote `q_e` applies when traversing from `u` to `v`; the reverse quote is `−q_e`. The motivating interpretation is a **logarithmic exchange rate**. Select positive confidence weights `w_e>0`. An internally consistent quote has the form

`q_e = φ_v − φ_u`

for node log-price potentials `φ`. Write `D∈R^(m×n)` for the oriented incidence/gradient matrix, with row `e` equal to `−1` at `u` and `+1` at `v`. Set `W=diag(w)`. The weighted inconsistency cost is

`E(q) = min_φ (q−Dφ)^T W (q−Dφ)`.

An edge quote is thus a freely signed datum, including both traversal directions. Actual fee-bearing transactions are directed and generally lack reverse symmetry. CHTR-01 covers those inequalities; CHTR-02 measures reversible **quote consistency**. The exact `Fraction` program accepts rational additive quotes. Natural logarithms of rational exchange rates need not be rational; rational inputs are synthetic or explicitly rounded values, and the algebra operates exactly on those inputs.

## CHTR-02/T1: fundamental cycles are a complete obstruction

Select any spanning tree. Every non-tree edge (chord) creates a unique fundamental cycle: traverse that chord in its orientation and return along the tree. Let `C∈R^(β×m)` contain the corresponding signed edge vectors, with `β=m−n+1`. Then

`C D = 0`, and `rank C = β`.

**Claim.** There exists a potential `φ` with `q=Dφ` if and only if `Cq=0`. The potential is unique up to a global additive constant.

**Proof.** The forward direction follows by telescoping along every closed walk. For the reverse direction, assign the root vertex potential zero and integrate `q` along the unique tree path to each vertex. All tree-edge equalities then hold. Each chord equality follows because the signed sum around its fundamental cycle vanishes. Connectedness makes any two solutions differ by a constant. Each cycle row contains its own chord with coefficient `1` and zero entries at all other chords, proving linear independence and the stated rank. QED.

A tree has `β=0` and every quote is a gradient. Parallel edges are permitted; they form a genuine length-two fundamental circulation. Self-loops are excluded by the implementation.

## CHTR-02/T2: the weighted cycle-Gram identity

Define the cycle coordinates `h=Cq` and the positive-definite matrix

`G = C W^(-1) C^T`.

**Theorem (exact minimum-energy certificate).**

`E(q) = h^T G^(-1) h`.

The unique optimal **edge residual** is

`r* = W^(-1) C^T G^(-1) h`.

The optimal potential, with any chosen root gauge, is recovered by integrating `q−r*` along the spanning tree. Its residual satisfies the exact zero-divergence equation `D^T W r* = 0`.

**Proof.** Independence of the rows of `C` and positivity of `W` make `G` positive definite. With `λ=G^(-1)h`, the displayed residual has `Cr*=h`. By T1, `q−r*` equals a vertex gradient. For any competing potential and residual `r'=q−Dφ`, we have `Cr'=h`. Thus `d=r'−r*` lies in `ker C`. Since `Wr*=C^T λ`, the cross term vanishes: `d^T Wr*=d^T C^T λ=(Cd)^T λ=0`. Consequently,

`(r')^T W r' = (r*)^T W r* + d^T W d ≥ (r*)^T W r*`.

Positive weights make equality possible only when `d=0`. Finally,

`(r*)^T W r* = λ^T C W^(-1) C^T λ = h^T G^(-1)h`.

The weighted divergence vanishes because `D^T W r*=D^T C^T λ=0`. QED.

The formula also holds for `β=0` with empty cycle matrices interpreted as zero energy.

### Concrete triangle

For the oriented triangle `0→1→2→0`, let `q=(1,0,0)` and `w=(1,1,1)`. Then `C=(1,1,1)`, `h=1`, `G=3`, and

`E(q)=1/3`, `r*=(1/3,1/3,1/3)`.

The root-gauge optimizer is `φ=(0, 2/3, 1/3)`. All these quantities are rational and independently checked in the oracle.

## CHTR-02/T3: gauge and orientation invariance

For arbitrary vertex values `ψ`, replacing `q` by `q+Dψ` leaves `Cq`, `r*`, and `E(q)` unchanged. The minimizing potential shifts by `ψ` up to a root-gauge correction.

**Proof.** Since `CD=0`, cycle coordinates and the explicit residual are unchanged. Equivalently, set `φ'=φ+ψ` in the minimization. Reversing an edge and negating its quote leaves the squared residual and hence the optimum unchanged. QED.

This is the additive analogue of the holonomy invariants explored in [RSITopology](https://github.com/MoralityLabAI/RSITopology) and [Goodfireverse](../goodfireverse/GRAM_HOLONOMY.md). The analogue concerns mathematical gauge structure; the spaces and experimental interpretations differ.

## CHTR-02/T4: every circulation supplies a certified lower bound

For **any** nonzero signed circulation `z∈ker D^T`, including linear combinations of fundamental cycles,

`E(q) ≥ (z^T q)^2 / (z^T W^(-1) z)`.

**Proof.** The circulation annihilates every gradient, so `z^T q=z^T r*`. Weighted Cauchy–Schwarz bounds its square by `(z^T W^(-1)z)(r*^T W r*)`. QED.

On a connected graph with exactly one independent cycle, equality holds for its fundamental cycle, by T2. For general graphs, the largest bound over individual fundamental cycles is conservative; the full Gram inverse accounts for coupled cycles.

## CHTR-02/T5: global error-ball certification

Suppose the measured quote is `q`, while the unknown true quote `q'` satisfies independent additive error bars `|q'_e−q_e|≤η_e`, with `η_e≥0`. Let `Δ²=Σ_e w_e η_e²`.

**Theorem.** If `E(q)>Δ²`, **every** admissible `q'` has `E(q')>0`.

**Proof.** Let `S=im D`. The distance to a fixed nonempty subspace is 1-Lipschitz: `|dist_W(x,S)−dist_W(y,S)|≤||x−y||_W`, by the triangle inequality and taking infima. Here `dist_W(q,S)=sqrt(E(q))` and `||q−q'||_W≤Δ`. Hence `sqrt(E(q'))≥sqrt(E(q))−Δ>0`. QED.

This is a statement about inconsistency of some cycle, **not** a profit forecast. A failure of the strict inequality is inconclusive.

## CHTR-02/T6: an exact interval certificate for a chosen cycle

The global bound can be weakened by uncertain edges that lie on bridges. For a nonzero signed circulation `z`, define

`H=|z^T q|`, `U=Σ_e |z_e| η_e`, `S=z^T W^(-1) z`.

**Theorem (robust cycle lower bound).** Every admissible true quotation satisfies

`E(q') ≥ max(0,H−U)^2 / S`.

**Proof.** The triangle inequality gives `|z^T q'|≥max(0,|z^T q|−Σ|z_e||q'_e−q_e|)≥max(0,H−U)`. Apply T4 to `q'`. QED.

**Sharpness for the unicyclic case.** If `β=1` and `z` generates the cycle space, then the right-hand side is exactly `min_{|q'−q|≤η} E(q')`. Indeed, the independent error box maps under the linear functional `z^T` onto the entire interval `[z^Tq−U,z^Tq+U]`. Its element nearest to zero attains the right-hand side because T2 reduces the energy to `(z^Tq')²/S`.

For a triangle with `q=(1,0,0)`, `w=(1,1,1)` and `η=(1/5,1/5,1/5)`, the exact worst-case energy is `4/75`, attained at `q'=(4/5,−1/5,−1/5)`. Adding a fourth bridge edge carrying weight `100` and error allowance `10` makes the global T5 test inconclusive but leaves this cycle bound unchanged.

## CHTR-02/T7: the cycle certificate reconstructs the optimum

A machine-checkable finite certificate consists of a spanning tree, fundamental cycle rows `C`, their Gram matrix `G`, dual solution `λ`, root-normalized potential `φ`, and residual `r`. Verify:

1. Each row is a circulation, `CD=0`, and the chord columns form an identity.
2. `G=CW^(−1)C^T`, `Gλ=Cq`, `r=W^(−1)C^Tλ`.
3. `q−r=Dφ` and `E=Σw_e r_e²=λ^T Cq`.

These equalities imply that `φ` minimizes the weighted squared residual, by the Pythagorean identity proved in T2. The `Fraction` code verifies the last two lines on every test and constructs fundamental cycles from a spanning tree. A standalone untrusted-certificate verifier is the next engineering step; its admissibility and input checking should be independent of the constructor.

## Numerical and formal verification

The standard-library module [hodge_arbitrage.py](hodge_arbitrage.py) uses only exact `Fraction` arithmetic. The [tests](../../tests/test_hodge_arbitrage.py) include exhaustive single-cycle configurations, a reproducible 150-case multicycle scan, gauge and edge-orientation transformations, disconnected and malformed input checks, sharp interval examples, a graph containing a bridge, and mixed fundamental-cycle lower bounds.

```sh
python -m unittest tests.test_hodge_arbitrage -v
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/Hodge.lean
```

The Lean module formalizes walk concatenation, gauge telescoping, closed-path invariance, closed potential exactness, and edge-residual gauge cancellation over `Int`. Its `#print axioms` outputs are checked by the existing workflow. The matrix identity and inequality proofs above remain pencil-and-paper proofs pending a Lean linear-algebra library and corresponding kernel verification.

## Next hard challenge: nonlinear hook curvature

When finite trade amounts alter the marginal rate along a path, `q_e` depends on inventories, order size and possibly hook state. A fixed edge 1-cochain then ceases to model the routing problem. One candidate extension is an **integrated exchange connection** whose path holonomy measures the effect of reserve evolution. To get a meaningful obstruction theorem, specify a deterministic shared state transition, require path-replay semantics, and test whether a gauge-invariant path functional can provide either a conservative upper bound on attainable gain or a paired counterexample. Explicitly handle noncomposable hooks; the Chitra–Kulkarni–Srinivasan routing work treats such constraints as a substantive part of execution, not merely a reweighting of static edges.
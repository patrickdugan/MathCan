# COE-01: chromatic observer dimension and stable probe extension

**Date:** 2026-11-15. **Status:** new, self-contained finite theorem with exact computational witnesses and partial Lean certificates; no claim of priority over the mathematics literature. The theorem is an elementary graph-coding observation presented here for task-relative compactification. Its verification is separate from claims in the two source manuscripts.

## Motivation and source separation

- [OpenAI Math family 098](https://github.com/openai/math/blob/main/lean/docs/098.md), *A doubling Hilbert subset with no finite-dimensional bi-Lipschitz embedding* (September 25, 2026), constructs an obstruction to globally faithful metric dimension reduction, even for compact doubling Hilbert subsets. Its published Lean comparator has a more specific scope than the whole family.
- [OpenAI Math family 332](https://github.com/openai/math/blob/main/preprints/Metric-Markov-Cotype-Two-of-l1-October-5-2026/README.md), *Metric Markov Cotype Two of ℓ1* (October 5, 2026), claims a universal-loss Lipschitz extension from arbitrary Hilbert subsets into ℓ1. The present work uses the distinction between stable forward observables and inverse metric fidelity; it neither assumes the manuscript has been independently certified nor reproduces its deep proof.

The following theorem is proved directly using finite graph coloring, binary codes, and scalar McShane extension, so its truth is independent of those source manuscripts. The fact that it is *new to this repository* is verified; literature-wide mathematical novelty remains unassessed.

## The chromatic observer and extension theorem

Let `G=(V,E)` be a finite simple graph with `n>=1` vertices and chromatic number `χ(G)`. Identify its vertices with unit vectors `e_v` in `H=R^n`, and let `S={0} ∪ {e_v : v∈V}`. A `k`-bit observer is an assignment `c:V→{0,1}^k`. The evaluator distinguishes exactly the edges `uv∈E`: it requires `c(u) ≠ c(v)` for those pairs.

**Theorem COE-1 (exact task-relative dimension).** The minimum number of binary features is

```
                 k_0(G) = ceil(log_2 χ(G)).
```

For any optimal observer there is an extension `F:H→[0,1]^k`, with `F(e_v)=c(v)` and `F(0)=(1/2,...,1/2)`, such that

```
              ||F(x)-F(y)||_∞ ≤ ||x-y||_2.
```

Hence the same extension, viewed in `ℓ1^k`, has Lipschitz constant at most `k`. This explicit factor `k` is only our elementary coordinatewise bound. Family 332's universal ℓ1 extension result concerns arbitrary ℓ1-valued Lipschitz data, and is logically stronger.

*Proof.* A separating observer assigns distinct binary words across every edge; treating each distinct word as a color gives a proper coloring using at most `2^k` colors, so `χ(G)≤2^k`. Conversely, give vertices an optimal χ-coloring and encode each color with `k_0` bits. For the extension, set `f_j(e_v)=c(v)_j` and `f_j(0)=1/2`. Distances between different spokes equal `√2`, and each spoke is unit distance from zero. Thus each coordinate `f_j` is 1-Lipschitz on `S`. Define

```
 F_j(x) = clip_[0,1] ( min_{s∈S} [ f_j(s) + ||x-s||_2 ] ).
```

The infimum of 1-Lipschitz cones is 1-Lipschitz and agrees with `f_j` on `S`; clipping preserves both properties. Taking the maximum over coordinates proves the result. ∎

**Theorem COE-2 (robust coding bounds).** Let `k_r(G)` be the fewest bits in an observer satisfying `d_H(c(u),c(v))≥r` on every tested edge. Then, for every integer `r≥1`,

```
  ceil(log_2 χ(G)) ≤ k_r(G) ≤ r * ceil(log_2 χ(G)).
```

The upper bound repeats every bit of an optimal `k_0` observer `r` times. An observer with margin `r` survives any `r-1` feature erasures on all tested edges. For `r=2t+1`, the radius-`t` Hamming error balls around the endpoints of each edge are disjoint, so an evaluator that knows the tested pair can recover its identity after at most `t` flips.

For each clique of size `m`, the ordinary sphere-packing inequality supplies the **necessary** condition

```
       m * sum_{j=0}^t binom(k,j) ≤ 2^k
```

at a `2t+1` flip margin. This is a clique-specific obstruction, with no claim that the graph's chromatic number can replace `m` in the sphere-packing expression.

*Proof.* A margin-r observer separates edges, yielding the first inequality. Bit repetition gives the second. Removing fewer than r positions leaves at least one difference. Two radius-t Hamming balls intersect only if their centers have distance at most 2t, by the triangle inequality. On a clique, all m balls are pairwise disjoint, each of cardinality `sum binom(k,j)`. ∎

**Finite sharp cell.** For `G=K6`, one-bit separation has exact width 3. Under one-bit flip tolerance (`r=3`) the exact width is **6**. A five-bit code would need `6*(1+5)=36` positions for disjoint radius-one balls inside `2^5=32` available positions, impossible. The six six-bit words `0,7,25,30,42,45` have pairwise Hamming distance at least three. The Lean module checks their range, pairwise margins and the integer packing obstruction; the general packing lemma is written here.

## The metric-quotient strengthening

The Hilbert-star construction is a special case of a stronger metric theorem. Let `(X,d)` be any nonempty **finite metric space**, `L>0`, and `E` an undirected evaluator graph on X. Form the **forced-identification graph** `H_L` by joining every two distinct points with `d(x,y)<1/L`. Let `π:X→Q` be its connected-component quotient. A binary observer `c:X→{0,1}^k` is `L`-Lipschitz into ℓ∞ exactly when it is constant on each connected component of `H_L`.

**Theorem COE-3 (exact metric-constrained chromatic observer).** If an evaluator edge joins two points in the same forced-identification component, no finite-width L-Lipschitz binary observer can satisfy the test. Otherwise, let `G_Q` be the evaluator graph induced on `Q`. Then

```
          min_L-Lipschitz observer bits = ceil(log_2 χ(G_Q)).
```

Every resulting observer on X extends to any ambient metric space containing X as an `L`-Lipschitz function with values in `[0,1]^k`, measured in ℓ∞. In particular this applies to Hilbert activations.

*Proof.* Whenever `c(x)≠c(y)`, two binary vectors differ in some coordinate by exactly 1, so the Lipschitz condition forces `1≤L d(x,y)`. This shows c is constant across `H_L` edges and consequently across connected components. Evaluator edges internal to one such component are therefore infeasible. For the converse, color `G_Q` optimally using χ distinct binary words in `k=ceil(log2 χ)` coordinates, and pull the code back along π. If x,y lie in the same component their codes agree. Across distinct components, `(x,y)` is no edge of `H_L`, hence `d(x,y)≥1/L`. As binary codes are at most unit distance apart in ℓ∞, the pulled-back observer is L-Lipschitz. Any evaluator-respecting observer yields a proper coloring of `G_Q`, giving the matching lower bound. Extend each coordinate by `clip_[0,1](inf_{s∈X}[c_j(s)+L d(x,s)])`; the standard cone argument finishes. ∎

This result makes an additional obstruction explicit: *short-edge connectivity can force globally identical binary readings even for points whose direct distance exceeds `1/L`*. On the real line with samples `0, 3/5, 6/5` and `L=1`, all points belong to one connected `H_L` component. The evaluator request to distinguish endpoints is impossible, even though their direct distance is `6/5 > 1`. Increasing L to 2 splits all three points into separate components, making a one-bit task observer feasible. At the exact boundary `d=1/L`, different bits are permitted.

For robust Hamming-margin r observables the same forced-identification quotient applies, because the output ℓ∞ distance of any distinct binary codes remains 1. The COE-2 color-repetition upper bound therefore holds on `G_Q` whenever the instance is feasible. An ambient Lipschitz extension takes values in the continuous cube; its intermediate points may have fractional coordinates, as required by continuity on connected Hilbert spaces.

## The exact critical Lipschitz constant and width staircase

Let `rho(u,v)` denote the **minimum bottleneck distance** between distinct vertices of a finite metric space:

```
    rho(u,v) = min_{finite paths u=x0,...,xm=v}
                         max_{0<=i<m} d(x_i,x_(i+1)).
```

For each evaluator edge `uv`, this is the smallest maximum jump needed to connect its endpoints. Since X is finite and has strictly positive distances between distinct points, `rho(u,v)>0` for `u!=v`. The complete weighted graph supplies a path, so the minimum is attained.

**Theorem COE-4 (exact feasible Lipschitz threshold).** For a nonempty evaluator edge set E, define

```
                       L_* = max_{uv in E} (1/rho(u,v)).
```

A finite-width, binary, `L`-Lipschitz evaluator observer exists **exactly when `L>=L_*`**, with equality included. If E is empty, every `L>=0` permits a constant observer; take `L_*=0`. For positive L in the feasible regime, define `k(L)` as the minimum bit count. Then `k(L)` is a nonincreasing, integer-valued staircase; its only possible jump locations lie among the reciprocals `1/d(x,y)` of the positive pairwise metric distances. The values at the jump locations use the **new**, weaker equivalence relation.

*Proof.* Two vertices lie in one connected component of `H_L` if and only if they admit a path all of whose edge distances are **strictly** less than `1/L`. By finiteness, this holds exactly when `rho(u,v)<1/L`. Theorem COE-3 makes every evaluator edge feasible precisely when `rho(u,v)>=1/L`, i.e. `L>=1/rho(u,v)`. Taking their maximum gives the critical constant. At equality the strict short-edge condition excludes a bottleneck edge of length exactly `1/L`, so feasibility holds. If `L2>=L1>0`, any binary observer that satisfies the L1-Lipschitz bound also satisfies the L2 bound; minimizing over a larger feasible set shows `k(L2)<=k(L1)`. Finally `H_L` changes only when the strict inequality `d(x,y)<1/L` switches truth value at `L=1/d(x,y)`. Since G stays fixed, its quotient and hence chromatic width stay fixed between consecutive such thresholds. ∎

**Exact rational witnesses.** On line samples `0,3/5,6/5`, the bottleneck path from first to last has jump size `3/5`; `rho=3/5`, so an evaluator separating the endpoints has the exact critical constant `L_*=5/3`. At `L=49/30` it is impossible, while at `L=5/3` it admits a one-bit observer. A second example has line samples `0,3,6,1/5` and evaluator path edges `(0,1),(1,2),(2,3)`. At `L=1`, short-distance identification merges vertices 0 and 3, creating a triangle in the quotient and requiring two bits. At `L=5`, all four vertices separate and one bit suffices. The exact-rational Python oracle computes `rho` with min/max Floyd-Warshall and checks these cases separately from the observer solver. A further exhaustive four-state harness compares the bottleneck threshold with direct feasibility for each of 64 evaluator graphs across rational Lipschitz values, including exact critical equality.

These statements concern **finite sampled metric spaces** and binary `ell_infinity` observables. The minimax bottleneck and graph-coloring principles are standard mathematical constructions; the combined evaluator-specific formulation is a research contribution to this program, with literature-wide priority unassessed.

## Scope and limitations

The graph represents **evaluator-relevant pairs**, rather than all Hilbert distances. The COE-3 quotient incorporates local metric constraints before coding. Two vertices with the same observer code may be geometrically separated, and the extended observer need not have a Lipschitz inverse. The construction is thus compatible with the obstruction in family 098. Finite-dimensional ℓ1 extension with optimal universal constant, all graphs' robust coding numbers and the genuine compact doubling construction of family 098 remain separate questions.

## Reproduce

The companion reference in `MoralityLabAI/Compactification-Theory/research/chromatic_observer_gym_v1` implements exact graph coloring, minimal robust observer search, the explicit extension and regression tests. Its deterministic suite enumerates all 64 simple graphs on four vertices and checks metric-quotient equivalence, transitive forced identifications strict threshold behavior, exact critical Lipschitz values and a decreasing chromatic-width staircase. The MathCan Lean module uses the repository's `leanprover/lean4:v4.35.0` `Init` toolchain and reports the transitive axioms of each finite lemma. Source results are not imported as axioms.
# COE-02: integer cut capacity, stable binary probes and an unbounded relaxation gap

**Date:** 2026-11-15. **Research status:** self-contained new-to-program mathematics with exact small-instance witnesses. No claim of literature-wide priority. The general finite-metric and equilateral theorems below have written proofs; the companion Lean module certifies selected finite cases, not the general statements.

## Motivation and sources

This develops [COE-01](CHROMATIC_OBSERVER_THEOREM.md), which was motivated by two manuscripts in OpenAI's October 2026 mathematics collection:

* [#098, A doubling Hilbert subset with no finite-dimensional bi-Lipschitz embedding](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-doubling-Hilbert-subset-with-no-finite-dimensional-bi-Lipschitz-embedding-September-25-2026/main.pdf). Global metric reconstruction can be impossible even for doubling Hilbert subsets.
* [#332, Metric Markov Cotype Two of ℓ1](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Metric-Markov-Cotype-Two-of-l1-October-5-2026/l1-markov-cotype.pdf). The manuscript claims a universal-loss extension of ℓ1-valued Lipschitz maps defined on Hilbert subsets.

COE-01 controls binary observers in `ell_infinity`, where any two distinct bitwords are exactly distance one. The present result controls the **whole feature-distance budget in `ell_1`**, where every bit that changes across a pair consumes one unit. It is a finite combinatorial theorem established without assuming the claimed source-paper theorems. An infinite-dimensional Lipschitz extension is a separate question.

## COE-5: exact integer cut-capacity formulation

Let `(X,d)` be a nonempty finite metric space of `n` distinct states, with evaluator graph `E` and desired Hamming margin `r >= 1`. A binary observer `c:X -> {0,1}^k` is admissible at Lipschitz budget `L >= 0` when

```
   d_H(c(u),c(v)) >= r            for uv in E
   d_H(c(u),c(v)) <= L * d(u,v)   for all distinct u,v in X.
```

Choose one representative from every nonconstant cut `S | X\S`, orienting cuts so a designated state `x0` lies outside `S`. Write `delta_S(u,v)=1` when exactly one of `u,v` belongs to `S`, and zero otherwise. Let `B_uv=floor(L*d(u,v))` for all unordered distinct pairs.

**Theorem (exact finite integer program).** An admissible width-`k` observer exists if and only if there are nonnegative integer cut multiplicities `m_S` satisfying

```
   sum_S m_S*delta_S(u,v) >= r         for uv in E
   sum_S m_S*delta_S(u,v) <= B_uv      for all distinct u,v
   sum_S m_S <= k.
```

Consequently, the minimum width equals the minimum `sum_S m_S` over feasible integer cut multiplicities. If no feasible multiplicities exist, no finite width can satisfy the task under the specified `ell_1` Lipschitz budget.

*Proof.* Each nonconstant coordinate of a binary observer partitions X into its zero-set and one-set. Complement the coordinate if necessary to place `x0` in the zero-set. Its contribution to Hamming distance on `(u,v)` is precisely `delta_S(u,v)`. Grouping repeated cuts produces the integers `m_S`. Constant coordinates can be removed. Conversely, repeat the indicator of each cut `S` exactly `m_S` times. The resulting words have the stipulated pairwise Hamming distances. Integer-valued distances satisfy `D_uv<= L*d_uv` precisely when `D_uv<=floor(L*d_uv)`. Adding at most `k-sum m_S` constant bits gives exact width `k`, if requested. ∎

**Finite-decision corollary.** Any feasible solution with nonconstant coordinates obeys

```
      (n-1) * sum_S m_S <= sum_{u<v} B_uv.
```

Indeed, every nontrivial cut crosses `|S|(n-|S|) >= n-1` unordered pairs. Thus a finite BFS over pair-load vectors `D_uv in {0,...,B_uv}` is a complete decision procedure. The companion oracle deduplicates identical load vectors and returns a minimum-width cut multiset. A user-specified search-size guard raises an explicit resource exception rather than reporting infeasibility.

## COE-6: dual lower certificates

Take nonnegative rational evaluator weights `alpha_e`, and nonnegative rational pair weights `beta_p`. Suppose **every** nontrivial cut obeys

```
  sum_{e in E} alpha_e * delta_S(e)
        <= 1 + sum_{p in pairs(X)} beta_p * delta_S(p).
```

Then every admissible binary observer satisfies the checkable lower bound

```
  k >= ceil(r * sum_e alpha_e - sum_p beta_p * B_p).
```

*Proof.* Multiply each cut inequality by its integer multiplicity `m_S` and sum over S. The lower margin constraints imply the left side is at least `r sum_e alpha_e`. The total cut count contributes `k`, while the pair capacity terms are at most `sum_p beta_p B_p`. Rearranging yields the bound. ∎

This certificate uses rational arithmetic and a finite enumeration of all canonical cuts. It can certify width lower bounds without trusting an optimization solver's internal search. Integrality can require stronger obstructions than these linear certificates.

## COE-7: exact equilateral feasibility and width cliffs

Consider an equilateral space of `n>=2` points, `d(u,v)=1` for `u!=v`, with `r=1`.

**Theorem (Lipschitz phase at 1 and 2).** For a nonempty evaluator graph G:

* `L<1`: the evaluator is infeasible.
* `1<=L<2`: an observer exists exactly when G is bipartite; when it exists, minimum width is 1.
* `L>=2`: every finite evaluator graph is feasible; at `L=2`, width is at most `chi(G)-1` by assigning the zero word and distinct unit words to its colors.

*Proof.* An evaluator edge demands one Hamming unit, hence `L>=1`. If `L<2`, the integer pair capacities equal one. A subset of a Hamming cube with all pairwise distances at most one has at most two distinct words: after XOR-translating one word to zero, all other words have Hamming weight one, and two different unit words are distance two. Therefore all evaluator distinctions can be represented only by a two-coloring. A bipartition supplies the corresponding one-bit observer. At `L=2`, assign the first color zero and the others separate unit words. Their pairwise distances lie in `{0,1,2}`, with edges separated. ∎

An odd evaluator cycle is therefore infeasible at `L=1` **regardless of how many binary probes are supplied**, despite every direct metric distance meeting the single-edge requirement. This is a global parity/cube-geometry obstruction absent from the `ell_infinity` observer theorem.

**Theorem (sharp complete-graph cost at L=2).** For the complete evaluator `K_n` on the equilateral metric, the minimum binary width at `L=2`, `r=1`, is

```
     k(K_2)=1,  k(K_3)=2,  k(K_4)=2,
     k(K_n)=n-1 for every n>=5.
```

*Proof.* An admissible `K_n` observer assigns `n` distinct vertices of a k-dimensional binary cube whose diameter is at most two. For `k=1` there are at most two words, and for `k=2` at most four. For `k>=3`, any diameter-two subset `A` has size at most `k+1`. To prove this, XOR-translate so `0 in A`; every remaining word has weight one or two. If there are no weight-two words, at most `k` unit words remain. Otherwise the family F of supports of weight-two words consists of pairwise intersecting 2-subsets. Unit words can use only coordinates in the intersection of all members of F. If F is a singleton then `|A|<=4<=k+1`. If F has a common coordinate and at least two members, F is a star of size at most `k-1`, and at most its central unit word may occur, so `|A|<=k+1`. If F has empty total intersection, any pairwise-intersecting family of 2-subsets is a triangle with at most three members, and no unit word is allowed, giving `|A|<=4<=k+1`. Thus `n<=k+1` for `k>=3`. The zero word together with `n-1` distinct unit words attains dimension `n-1`; `K_4` is realized by the whole two-bit cube. ∎

For `K_5`, **`ell_infinity` at `L=1` needs 3 bits**, while **`ell_1` at `L=2` needs 4** and **`ell_1` at `L=3` needs 3**. Exact words at `L=2`: `0000,0001,0010,0100,1000`. The three-bit lower bound at `L=2` has a simpler finite proof: among five selected vertices of the 3-cube, two must be antipodal, hence distance three. Lean checks the 256-subset-mask pigeonhole certificate and the four-bit constructive witness.

## COE-8: unbounded integrality gap of soft cut relaxation

Relax COE-5 by allowing real `m_S >= 0`. This is a *fractional cut-mass relaxation*, not a physical number of binary coordinates. Let `N=binom(n,2)` and `C=floor(n^2/4)`, and retain the equilateral complete evaluator `K_n` at `L=2`, `r=1`.

**Theorem (sharp fractional optimum).** The fractional program has optimum exactly

```
                     LP_n = N/C.
```

*Proof.* Every cut crosses at most `C` of the `N` unordered pairs. Summing the `N` evaluator lower bounds yields `N<= C * sum_S m_S`, giving `LP_n>=N/C`. For equality, take every balanced unordered partition `S|X\S` with `|S|` equal to either `floor(n/2)` or `ceil(n/2)`. Every such cut crosses exactly `C` pairs. There are `T` balanced cuts, and permutation symmetry shows that each pair is crossed by exactly `T*C/N` of them. Give each balanced cut weight `N/(T*C)`. Every pair then has fractional load exactly one, satisfying both lower bound one and upper capacity two; total cut weight is `N/C`. ∎

Combining this with the integer anticode theorem gives an **unbounded multiplicative integrality gap** for every `n>=5`:

```
    integer_optimum / LP_n
      = (n-1) * floor(n^2/4) / binom(n,2)
      = 2 * floor(n^2/4) / n ~ n/2.
```

For `K_5`, the ten balanced cuts each receive weight `1/6`; every pair has load 1, so the fractional value is `10/6=5/3`. The smallest realizable binary observer has width 4, a gap of `12/5=2.4`. The all-edge dual weights `alpha_e=1/6` and `beta_p=0` certify the exact fractional optimum `5/3` from the COE-6 inequalities. More generally, `alpha_e=1/C` gives the sharp dual fractional certificate on `K_n`.

A soft allocation of fractional cut-mass can therefore assign a dimension-like cost bounded near two while quantization into individual binary features costs linearly many coordinates. The mathematical source of the gap is Hamming cube geometry. Whether a particular SAE or recurrent probe exhibits a comparable learning gap is an experimental question.

## COE-9: finite Lipschitz width staircase

As `L` increases, all pair capacities `B_uv=floor(Ld_uv)` weakly increase. The admissible set of integer cut multisets therefore expands, so the exact minimum width (where defined) is nonincreasing. A change can occur only when some `L*d_uv` passes an integer, i.e. at `L=h/d_uv` with positive integer h. All breakpoints are included at equality. This is a distinct staircase from COE-04's `ell_infinity` bottleneck-quotient staircase; neither requires a closed-form coloring algorithm for the general `ell_1` case.

## Applied benchmark, validation and scope

The companion [Compactification-Theory COE-02 gym](https://github.com/MoralityLabAI/Compactification-Theory/tree/feat/coe01-chromatic-observer-20261115/research/chromatic_observer_gym_v1) adds exact cut enumeration, load-vector BFS, independently checked rational lower certificates, a frozen activation/evaluator JSON adapter, and a synthetic `K_5` one-hot latent fixture.

* The frozen fixture has five mutually equidistant rational `ell_1` prototypes; it is explicitly **synthetic** and is not a trained-model or SAE activation capture.
* Ten local unittest methods pass. An independent brute-force word enumerator agrees with the cut-BFS oracle on all 8 three-vertex evaluator graphs, for Lipschitz budgets `0,1,2` and margins `1,2`.
* The checks include exact `K_5` Pareto points, the odd-cycle infeasibility certificate, rational line-metric threshold equality, dual-weight rejection, and exact balanced-cut identities for `2<=n<=9`.
* The Lean module checks finite `K_5` cut counts, 3-bit antipodal obstruction and explicit 4-bit witness under the pinned toolchain. General finite-metric, equilateral anticode and fractional-optimum theorems currently have written proofs only.

For transfer to looped transformers or SAEs, freeze a checkpoint and a held-out evaluator edge set, extract a **small** fixed collection of activation vectors, and preserve the metric/probe convention in the report. Compare best symbolic width with the performance of fitted continuous probes before binary quantization and after it. Report causal intervention outcomes separately. The present result gives a mathematical capacity boundary for this protocol; it supplies no empirical transformer capability claim.

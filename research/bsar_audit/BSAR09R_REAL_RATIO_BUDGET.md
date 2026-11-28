# BSAR-09R: real product and exponential control under a dimensionless window budget

This is the real-analysis companion to [BSAR-09 issue #186](https://github.com/patrickdugan/MathCan/issues/186) and the independent [BSAR-09 exact rational-window PR](https://github.com/patrickdugan/MathCan/pull/188). It is isolated inside MathCan's existing `experiments/deligne_mathlib` project, which pins Lean and Mathlib to **v4.35.0**. The main Init-only library and its dependency set are unchanged.

## Real theorem, with all hypotheses visible

Let `M : ℝ` be positive. Define sequences `I_n, D_n : ℕ → ℝ` satisfying for all local steps `n`:

```text
0 <= I_n
0 <= D_n
2 I_n <= M
M*(D_(n+1)-D_n) <= I_n * D_(n+1)
```

For a finite horizon `K`, suppose an independent budget `B : ℝ` satisfies

\[
\sum_{n=0}^{K-1}\frac{I_n}{M}\le B.
\]

The proposed Lean theorem `BSAR09Real.uniform_real_endpoint_bound` establishes

\[
D_K\le D_0\exp(2B).
\]

It is a genuine **real-valued, finite-K conditional theorem**. If one could supply the same finite `B` uniformly for all horizons approaching a candidate singular time, the bound would become uniform over those horizons.

The proof separates the source ODE to one-step factor, induction to a finite product, and the exponential estimate. The final estimate uses the pinned Mathlib theorem `Real.prod_one_add_le_exp_sum`, with explicit nonnegative factors.

## Source-level reasoning

From `0 ≤ D_(n+1)`, `2 I_n ≤ M` and the ODE, the familiar source proof implies `D_(n+1) ≤ 2 D_n`. It then gives the sharper real inequality

\[
D_{n+1}\le\left(1+\frac{2I_n}{M}\right)D_n.
\]

Induction yields

\[
D_K\le D_0\prod_{n<K}\left(1+\frac{2I_n}{M}\right).
\]

Mathlib's exponential product bound supplies

\[
\prod_{n<K}(1+2a_n)\le \exp\left(2\sum_{n<K}a_n\right)
\]

for nonnegative `a_n`. Substitute `a_n=I_n/M` and the supplied budget.

## What remains open

The original [BSA-R Step7](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/lean/Step7VorticityDirectionPdeRound6.lean) defines integer-valued arithmetic windows without a PDE-derived total ratio budget. This separate real theorem assumes that such windows exist and meet the stated hypotheses. It does not construct them from smooth vorticity fields and does not derive a bound on the total `I/M` contribution from finite energy.

A physically meaningful successor would define `I_n` through an actual vorticity-direction estimate, justify the time partition near a candidate singularity, preserve units, handle vortex zero sets, and prove a uniform bound for `Σ I_n/M` independent of window count. Any use of direction-cone regularity must specify its functional norm and constants.

## Verification

```sh
cd experiments/deligne_mathlib
lake update
lake exe cache get
lake env lean BSAR09/RealWindow.lean
```

[Dedicated CI](../../.github/workflows/bsar09r-real-product.yml) checks Lean kernel elaboration, prints the axioms of the five real lemmas, rejects `sorryAx` and preserves source-hash receipts. A passing proof establishes only the conditional theorem with the assumptions above.

# BSAR-05: finite-window doubling does not supply a uniform window count

Pinned source: [BSA-R Step7 Lean](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/lean/Step7VorticityDirectionPdeRound6.lean), particularly `LerayDoublingChain` and `step7_leray_quadratic_doubling_closure`. The [independent six-round kernel replay](https://github.com/patrickdugan/MathCan/pull/171) has verified that the original published Lean modules compile under 4.35.0 and their printed axiom checks contain no `Classical.choice` or `sorryAx`.

## The exact mathematical gap

The original Lean statement establishes a bound of the form

```text
hchain : LerayDoublingChain M K d0 dfinal
----------------------------------------
dfinal <= 2^K * d0
```

for a **given finite** number `K` of doubling windows, assuming the chain and local inequalities. To obtain a bound uniform over an arbitrarily long PDE trajectory, an argument needs an additional restriction on `K`, the growth factor per window, or both, derived from the dynamics and the actual energy budget.

BSAR-05's [Lean 4 countermodel](../../MathCan/BSARChainAudit.lean) copies the original inductive chain rules into a separate namespace and constructs a family

```text
M = 2,   Im = 1,   d0 = 1,   d_k = 2^k.
```

Every step satisfies:

```text
0 <= d_(k+1)
M * (d_(k+1) - d_k) <= Im * d_(k+1)
2 * Im <= M.
```

The proof shows that `LerayDoublingChain 2 k 1 (2^k)` holds for all natural `k`. It then proves that for every integer candidate cap there is a finite chain whose endpoint exceeds that cap, so no cap follows from the inductive rules alone.

This example is deliberately **arithmetic**, with an unbounded total sum of per-window `Im` costs when extended indefinitely. It is not a counterexample to the physical Navier–Stokes equations or to the stronger conclusion obtainable if one independently derives an appropriate **finite total enstrophy/energy budget** for actual solutions.

## Required analytic bridge

For the published regularity route, a successful next theorem should formalize at least:

- A PDE-derived inequality connecting actual enstrophy, vorticity-direction coherence, and the window `Im` budget.
- A partition/covering lemma showing a uniform bound on the number of doubling windows from a stated global energy constraint, with all constants explicit.
- Control of the direction-cone regularity factor `K_xi(t)` or its integrated contribution, sufficient to make that bound valid near a hypothetical singular time.

The BSA-R preprint itself names unconditional direction-cone integrability as the remaining target. BSAR-05 isolates the separate logical obligation needed to pass from finite window arithmetic to a global conclusion.

## Reproduce

```sh
lake env lean MathCan/BSARChainAudit.lean
```

The [dedicated GitHub Actions kernel gate](../../.github/workflows/bsar05-uniform-chain.yml) compiles the file under MathCan's pinned Lean 4.35.0 toolchain, captures source hashes and printed axioms, and rejects `sorryAx` or `Classical.choice`. This verifies only the restated arithmetic theorem and its associated countermodel.

# BSAR-06: a global charged-growth budget yields a K-independent endpoint bound

This follows [BSAR-05](https://github.com/patrickdugan/MathCan/pull/175), which kernel-checked arbitrarily long geometric chains satisfying the local integer `LerayDoublingChain` conditions from [BSA-R Step 7](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/lean/Step7VorticityDirectionPdeRound6.lean).

## Additional, explicit hypothesis

BSAR-06 defines a separate `MeteredChain`. Every local transition satisfies `d_next ≤ 2*d_previous`. If the step is a strict increase, its nonnegative `charge` must be at least one. The chain accumulates all charges into `used`, and a **global cap** `used ≤ B` is supplied as an independent assumption.

The intended kernel-checked result is

```text
0 ≤ d0
MeteredChain K d0 dlast used
used ≤ B
--------------------------------------
dlast ≤ 2^B * d0
```

with a recursively defined integer `Pow2`. The bound is independent of the number of windows `K`, because free windows must be nonincreasing. Charged windows can double, and each consumes at least one of the bounded global credits.

The proof uses induction on the chain plus monotonicity of `Pow2`. It also establishes that total charge zero forces the final state to be at most the initial state.

## Mathematical significance and remaining bridge

BSAR-05 demonstrates why the original local arithmetic alone permits geometrically growing endpoints as the number of windows increases. BSAR-06 gives an explicit *sufficient global condition* that blocks this pattern.

The new metering rule is a deliberately additional hypothesis. It has **not** been derived from the BSA-R `Im` terms or from three-dimensional Navier–Stokes. A valid application would require a theorem converting suitable PDE time-integrated estimates into an integer budget whose charges cover every harmful growth event, while keeping `B` uniformly bounded near a hypothetical singular time.

A finite-energy assumption alone cannot be substituted by name for this metering hypothesis without proving the relevant analytic estimate. The source remains a conditional, discrete theorem.

## Reproduce

```sh
lake env lean MathCan/BSARMeteredGrowth.lean
```

The [BSAR-06 CI workflow](../../.github/workflows/bsar06-metered-growth.yml) pins Lean via MathCan's toolchain, compiles the theorem, and archives its printed axiom dependencies. It rejects `sorryAx` and all axioms outside the explicitly reviewed set `propext`, `Quot.sound`, and `Classical.choice`. The current elaboration of the positive-cost arithmetic lemma uses Lean's standard `Classical.choice`; the claim is therefore a kernel-checked conditional arithmetic theorem under that declared logical foundation.

## Next RLT curriculum

Construct paired integer windows with the same initial state and horizon but different charge assignments. Train a compact verifier to detect a missing charge on a strict growth step, and separate a valid local-chain statement from a valid globally budgeted conclusion. Hold out entire budget regimes, with exact arithmetic as the first oracle and Lean-kernel traces for any generated formal statements.

# BSAR-07: exact cumulative-window accounting and the analytic boundary

**Source:** [BSA-R Step 7 at `80c62433`](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/lean/Step7VorticityDirectionPdeRound6.lean). This is a companion to [BSAR-05](https://github.com/patrickdugan/MathCan/pull/175), which formalizes finite doubling chains without a uniform bound, and [BSAR-06](https://github.com/patrickdugan/MathCan/pull/180), which establishes a uniform bound under a separate growth-charge budget.

## A missing piece of the discrete correspondence

The BSA-R Step 7 `LerayDoublingChain M K d0 dfinal` has one local witness `Im : Int` per transition, subject to

```text
0 <= dnext
M * (dnext - dm) <= Im * dnext
2 * Im <= M
```

The published constructor stores **only** the endpoints and step count, so the final proposition contains no sum of `Im` values. The formal proof of `dfinal <= 2^K * d0` is valid for the stated finite chain but cannot establish how many growth windows are permitted.

BSAR-07 adds `WindowChain M K d0 dfinal spent`, which records a *nonnegative integer* `Im : Nat` for each window and accumulates `spent := Σ Im` in a separate field. This is a **strictly stronger structure** than the original chain. A formal `forget_ledger` theorem projects it back to the exact BSA-R `LerayDoublingChain` type.

A growth step has `dm < dnext`. For positive `M`, the local inequality gives `M*(dnext-dm) > 0`, forcing `Im > 0`. Since `Im : Nat`, this implies `Im >= 1`. The half-budget inequality implies `dnext <= 2*dm`, as in BSA-R's own Lean proof.

These two facts certify the same `MeteredChain` used in BSAR-06 **with the exact ledger's `spent` value**. Therefore, given

```text
M > 0
d0 >= 0
WindowChain M K d0 dfinal spent
spent <= B
-------------------------------------
dfinal <= 2^B * d0
```

the endpoint bound is independent of the number of steps `K`.

## Why integer accounting does not yet establish PDE regularity

The crucial `Im >= 1` inference comes from **integer quantization**, with an unspecified unit of measure. Real integrals can be positive and arbitrarily small. For instance, the real-valued window `M = 2`, `I = 1/2`, `dm = 3`, `dnext = 4` satisfies

```text
M*(dnext-dm) = 2 = I*dnext
2*I = 1 <= M.
```

It increases while spending less than one unit. Scaling `M` and `I` together preserves the local dynamics but changes how many integer ledger units are charged. The new bound therefore cannot be identified with a scale-invariant physical enstrophy estimate.

A legitimate continuous bridge must track **dimensionless** ratios `I/M` and use a quantitative product or discrete Grönwall estimate. If `0 <= I_m <= M/2`, then

```math
(M - I_m) D_{m+1} <= M D_m
```

and for a positive endpoint this yields

```math
D_{m+1} <= (1 - I_m/M)^{-1} D_m.
```

Consequently, a proved global upper bound on the sum of `I_m/M` could control the product through logarithmic estimates. Such an estimate would have to be derived from the actual vorticity-direction dynamics, using precise function-space assumptions. It is **not** present in the original Step 7 Lean constructors or certified by BSAR-07.

The prior BSAR-05 construction spends one integer unit per doubling window and thus violates any uniform aggregate budget as the horizon increases. BSAR-07 makes exactly which additional budget premise would exclude those chains explicit.

## Reproduction and acceptance

```sh
lake build MathCan.BSARChainAudit MathCan.BSARMeteredGrowth
lake env lean MathCan/BSARWindowBudget.lean
```

The [dedicated CI workflow](../../.github/workflows/bsar07-cumulative-window-budget.yml) compiles the imported proofs, checks the three new theorem statements and axiom dependencies, and archives the output and SHA-256 source digest.

The next mathematical tasks are to prove a rational or real product bound, formalize physically meaningful definitions of `I_m`, and justify summability of those window contributions near candidate singularities. Independent analysis must connect these discrete certificates to the smooth Navier–Stokes PDE. Native compilation of an arithmetic statement never substitutes for that analytic argument.

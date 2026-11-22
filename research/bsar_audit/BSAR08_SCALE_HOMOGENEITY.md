# BSAR-08: scale-homogeneous window growth and the continuous budget frontier

The [original BSA-R Step7](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/lean/Step7VorticityDirectionPdeRound6.lean) proved an integer endpoint bound of `2^K` across `K` windows. [BSAR-05](https://github.com/patrickdugan/MathCan/pull/175) exhibits unbounded geometric finite chains; [BSAR-06](https://github.com/patrickdugan/MathCan/pull/180) derives a uniform bound when growth consumes finitely many integer units; [BSAR-07](https://github.com/patrickdugan/MathCan/pull/183) connects that meter to an explicitly accumulated nonnegative integer `Im` ledger.

The next natural question is which bound remains meaningful when the cost is a **continuous integral**, whose amount depends on the time window and the chosen physical units.

## A sharper, scale-homogeneous local inequality

Let `M, I, dprev, dnext : Int` satisfy

```text
0 < M, 0 <= I, 0 <= dnext,
2*I <= M,
M*(dnext - dprev) <= I*dnext.
```

The source's half-budget argument gives `dnext <= 2*dprev`. Since `I >= 0`, this yields

```text
M*(dnext-dprev) <= I*dnext <= 2*I*dprev.
```

Rearranging produces the **source-grounded local envelope**

```text
M*dnext <= (M+2*I)*dprev.
```

[`MathCan/BSARRatioWindow.lean`](../../MathCan/BSARRatioWindow.lean) kernel-checks this entirely with cross-multiplied integer arithmetic. Its companion rescaling theorem shows that multiplying `M` and `I` by a nonnegative integer leaves the local conditions intact.

When interpreted over positive real `M`, this envelope reads

\[
D_{m+1} \leq \left(1+\frac{2I_m}{M}\right)D_m.
\]

Unlike an unscaled `Im >= 1` integer-credit rule, it depends on the dimensionless ratio `I_m/M`.

## Positive growth with arbitrarily small relative cost

The file also constructs exact witnesses for every positive natural `n`:

```text
M = 2n,  I = 1,  dprev = 2n - 1,  dnext = 2n.
```

The conditions hold, including equality in the window ODE, while `dnext > dprev` and

\[
\frac{I}{M}=\frac{1}{2n}\leq\frac1n.
\]

Thus an arbitrarily small dimensionless cost can accompany a strict growth event. The property `I >= 1` in the integer ledger is not a fixed **physical** minimum charge; its unit size changes under rescaling. This is a concrete source of potential overclaim when a discrete certificate is interpreted as a continuous-energy statement.

## The next valid global argument

For `M > 0` and `0 <= I_m/M <= 1/2`, the original ODE also gives

\[
(1-I_m/M)D_{m+1}\leq D_m.
\]

The elementary inequality `(1-a)^{-1} <= 1+2a` for `0 <= a <= 1/2` implies the local bound above. Iterating over `K` windows yields the **analytic target**:

\[
D_K\leq D_0 \prod_{m=0}^{K-1}\left(1+\frac{2I_m}{M}\right)
\leq D_0\exp\left(\frac{2}{M}\sum_{m=0}^{K-1}I_m\right).
\]

The exponential/product estimate is stated here as standard real analysis and **has not been formalized by the present Init-only Lean module**. The relevant theorem would require a real-valued definition of the `I_m` windows and a bound on `\sup_K \sum_{m<K}I_m/M`, uniform as the candidate singular time approaches. A finite total physical energy integral can serve only if a rigorous inequality shows it controls this precise sum.

The [upstream Round 6 collaborator specification](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/navier_stokes/ROUND6_COLLABORATOR_SPEC.md) specifically leaves unconditional integrability of the high-vorticity `C^{1/2}` direction-cone constant unresolved. Its role in the proposed `I_m` estimate needs source-level mathematical definitions, including zero-set handling, boundary conditions, and full constants.

## Reproduce

```sh
lake env lean MathCan/BSARRatioWindow.lean
```

The [dedicated BSAR-08 CI](../../.github/workflows/bsar08-ratio-window.yml) checks all four stated **integer** theorems, audits axiom dependencies and preserves the compilation receipts. The integer results are local algebraic implications. They do not establish regularity for the three-dimensional Navier–Stokes equations.

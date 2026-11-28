# COE-07R: dihedral observer and unequal-label collision ledger

**November 15, 2026.** A self-contained finite theorem for cyclically recurrent observations. The result extends the earlier COE-07 phase-gauge ledger to **unknown observation direction**, repeated task labels, and the optimal in-sample decoder of a deterministic descriptor. Literature-wide novelty and priority have not been established.

## Definitions and theorem

Let `X` be a finite population with labels `ell:X->A`. A T-visit binary observer gives a word `W(x)`. The cyclic group `C_T` acts on words by rotations. The dihedral group `D_T` additionally reverses their order. Define `N(x)` as the least integer in the rotation orbit (necklace), `B(x)` as the least integer in the rotation/reversal orbit (bracelet), and `C(x)` as popcount. Thus there are nested equivalence relations:

```
  equality of W  refines  equality of N  refines  equality of B  refines  equality of C.
```

For any descriptor `Q:X->Qspace`, write

```
  n_(q,a) = #{x: Q(x)=q and ell(x)=a},
  n_q     = sum_a n_(q,a),
  E       = #{unordered {x,y}: ell(x) != ell(y)}.
```

The **exact unequal-label separation theorem** is

\[
D_\ell(Q)=E-\sum_q \left[\binom{n_q}{2}-\sum_{a\in A}\binom{n_{q,a}}2\right].
\]

*Proof:* Every eligible pair is either separated by Q or falls into one of its equivalence classes. Inside a class q there are `binom(n_q,2)` pairs, of which `sum_a binom(n_(q,a),2)` share their label and are ineligible. The remaining pairs are exactly the eligible descriptor collisions. Subtract these from E. Each pair falls into a unique class, so the sum is exact. This also covers repeated labels and empty classes.

Consequently

\[
\boxed{D_\ell(W)-D_\ell(C)
  = [D_\ell(W)-D_\ell(N)]
  + [D_\ell(N)-D_\ell(B)]
  + [D_\ell(B)-D_\ell(C)]}
\]

with each bracket nonnegative by the nested equivalence relations. The middle term measures **orientation-sensitive distinctions that survive uncertainty about the starting clock**. The last term measures distinctions encoded in dihedral-invariant temporal *shape* at fixed count. Pair gaps are exact integer ledger entries with no independence assumption.

## Sharp decoder theorem under descriptor coarsening

For `x` uniformly drawn from X, let an oracle choose the most frequent label within the observed class Q=q. The maximal possible *in-sample* correct fraction is

\[
\boxed{A_\ell(Q)=\frac{1}{|X|}\sum_q \max_{a\in A} n_{q,a}.}
\]

*Proof:* The choices for distinct observed q are independent. The best prediction for a class is a label attaining `max_a n_(q,a)`. The displayed sum counts all correctly predicted members and attains the upper bound. For a coarsening that merges two Q classes with label-count vectors `u=(u_a)` and `v=(v_a)`, the decrease in the correct numerator is precisely

\[
  \Delta_A = \max_a u_a + \max_a v_a - \max_a(u_a+v_a)\ge0.
\]

It is nonnegative because `u_a+v_a <= max u + max v` for every a. Repeated merges prove `A_ell(W)>=A_ell(N)>=A_ell(B)>=A_ell(C)`. This class-majority decoder uses the very labels it scores; applying the formula to pre-recorded truth-conditioned histories is an **oracle analysis**, not a generalization claim.

## Dihedral orbit-count identity

Let `n(T,w)` be the number of cyclic necklaces of T bits and fixed weight w. Reversal is a well-defined involution on the set of necklaces, since reversing a rotation is another rotation of the reversed word. Let `f(T,w)` count necklaces fixed by this involution. Every orbit under the involution has one or two necklaces, so the number `b(T,w)` of bracelets is exactly

\[
\boxed{b(T,w)=\frac{n(T,w)+f(T,w)}2.}
\]

For T=8, w=4, exact enumeration gives `n=10`, `f=6`, `b=8`. For T=8, w=3 or 5, `n=7`, `b=5`. These finite counts are independently checked by the companion Python reference. Every equality above follows from elementary orbit partitioning and is separate from the cited OpenAI Math manuscripts.

## Native empirical instantiation

The prior `LoopedTransformers` 7M pretrained TRM correctness telemetry, a truth-conditioned oracle, has `E=1795` unequal-target-digit pairs among the 64 stalled Sudoku boards. At T=8:

- `D(W)=1414`, `D(N)=1389`, `D(B)=1389`, `D(C)=1369`.
- The three lost/retained ledger entries are `(25, 0, 20)`.
- The descriptor-class majority-oracle numerators are `(30, 24, 24, 19)` out of 64 samples.

At T=16 the pair scores are `(1447,1428,1428,1422)`, giving `(19,0,6)`. These numbers are independently replayed from immutable source receipts in `MoralityLabAI/LoopedTransformers/mechinterp/phase_gauge07/dihedral_replay.py`. SHA-256 of the pretrained checkpoint is `932b5e0df4e90021c21a064d4e716154086c46fda7afa676ea294484a30e38c3`; the original benchmark SHA is `59459ae0bb60b75db5be017e5f41adead391f2abb0b8fb043cd331c0ee043811`.

## Formalization boundary

`MathCan/DihedralPhaseGauge.lean` proves the subtraction ledger from nested natural-number collision counts, the two-label cross-pair expansion and two-class majority inequality as applicable, plus exact integer cells for the source replay. This is a **partial** Lean formalization. The general classifier collision formula, the orbit quotient theorem and its Burnside interpretation have the complete mathematical proofs above and independent finite tests; Lean does not import or trust model outputs.

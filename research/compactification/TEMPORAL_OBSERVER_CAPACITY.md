# COE-04: Tied temporal cut codes, quantizer precision, and the innovation horizon

**Date:** 2026-11-15. **Research status:** self-contained mathematical proofs and executable finite certificates; literature-wide novelty has not been assessed. Companion application: `MoralityLabAI/Compactification-Theory/research/chromatic_observer_gym_v1/COE04.md`.

## Mathematical problem

An evaluator has a finite state space `X` with `n` possible meanings and a graph `G=(X,E)` specifying pairs it must distinguish. A frozen recurrent mechanism produces `z_{t+1}=F(z_t)` for `t=0,...,T-1`. A **single tied readout** `q` emits `k` binary features at every visit. Its transcript is

`C_T(x) = (q(z_0(x)), q(z_1(x)),...,q(z_{T-1}(x))) in {0,1}^{kT}`.

For the complete evaluator `G=K_n` on an equilateral metric with unit pair distance, impose the aggregate `ell_1` budget

`d_H(C_T(x), C_T(y)) <= 2` for all `x,y`,

alongside minimum Hamming separation `d_H(C_T(x), C_T(y)) >= r` for every distinct pair. Aggregate length is the information delivered through the observer, while `k` is instantaneous head width. The state `z_t` and its recurrence may contain more information than the observer transcript.

## Theorem 1: sharp time–head-width–robustness tradeoff

**Theorem (temporal diameter-two cut capacity).** Fix `n >= 5`, `T >= 1`, and integer separation margin `r >= 1`. Allow deterministic recurrent dynamics with a phase register and one tied readout. Under the conditions above, the exact smallest head width is

```
                     / ceil((n-1)/T),  if r=1,
       k_min(n,T,r) = | ceil(n/T),      if r=2,
                     \ infeasible,     if r>=3.
```

The same lower bounds hold for arbitrarily complex recurrent dynamics, even if each visit has an independently chosen readout.

**Proof, lower bounds.** Flatten the `T` outputs into a binary word of length `m=kT`; recurrence and tying cannot increase the number of coordinates in this transcript. Translate one word in the code by XOR so it is zero; this preserves all Hamming distances.

At margin one, every remaining nonzero word has Hamming weight either one or two. Its weight-two supports form a family of pairwise-intersecting two-element subsets: disjoint supports would differ in four coordinates. A pairwise-intersecting family of two-element sets is either a star (all containing one coordinate), or contained in a triangle. A star has at most `m-1` members; a triangle has at most three. When weight-one words are also present, each weight-two support must contain the coordinates of every weight-one word. An elementary case split yields at most `m+1` total codewords whenever `m>=3`. For `m<=2` the full cube has at most four points, so cannot encode `n>=5`. Hence `n<=m+1`, or `kT>=n-1`.

At margin two, all nonzero translated words have weight exactly two. Their supports are pairwise intersecting. As `n>=5`, this family has at least four members and therefore must be a star. A star contains at most `m-1` distinct edges. Thus `n<=m`, or `kT>=n`. Finally margin `r>=3` directly contradicts the aggregate Hamming cap two.

**Proof, constructions.** Set `m=kT`. When `r=1` and `m>=n-1`, use the `n` codewords `0,e_1,...,e_(n-1)`. Their pair distances are one or two. When `r=2` and `m>=n`, use `e_1,...,e_n`, each pair at distance two. Divide the `m` coordinates into `T` consecutive blocks of `k`. Define a shared-state machine with state `(symbol,phase)` and recurrence

`F(symbol,phase) = (symbol,phase+1)`;

let the **same** readout `q(symbol,phase)` emit the block of coordinates belonging to that phase. This realizes the code in `T` visits using exactly `k` binary heads. The phase register requires up to `ceil(log2 T)` bits of latent state in addition to the symbol; it is a deliberate resource in the construction, not an uncharged source of capacity. ∎

**Checks.** At `(n,T)=(5,4)`, the margin-one optimal observer uses one bit per visit and outputs `(1000),(0100),(0010),(0001),(0000)`; the margin-two optimum uses two bits per visit because five singleton positions are needed. A separate Python clique search over the four-bit cube confirms that the largest binary family with all pairwise Hamming distances exactly two has size four. The Lean file `MathCan/TemporalCutCapacity.lean` kernel-checks the five-state tied witness and Hamming-distance cases. **The Lean checker does not formalize the general extremal-set proof above.**

## Theorem 2: a finite innovation horizon under contraction

Suppose the recurrent map `F` is `alpha`-contractive, `0<=alpha<1`, on a normed space and fixes the same point `z_*` for all initial states. Let all `z_0(x)` lie at distance at most `R` from `z_*`. Let `q` be any `k`-bit quantizer that is constant on the open ball `B(z_*,delta)` for some `delta>0`. Define

`t_* = min {t in N: alpha^t R < delta}`.

**Theorem (late-observation collapse).** All readouts `q(z_t(x))` coincide across `x` whenever `t>=t_*`. Consequently an injective evaluator transcript for `n` states satisfies

`n <= 2^(k * min(T,t_*))`.

If `n>=5` and its transcript additionally satisfies the diameter-two condition from Theorem 1, the stronger necessary inequalities are

- `n-1 <= k * min(T,t_*)` at margin one;
- `n <= k * min(T,t_*)` at margin two.

**Proof.** Contraction and the fixed-point condition imply `||z_t(x)-z_*|| <= alpha^t R`. At `t>=t_*` the trajectory enters the common open quantizer cell, so the quantizer output is identical for every source state. The remaining observations are constant transcript suffixes. Only `k min(T,t_*)` binary coordinates can distinguish sources, establishing the counting bound. In the diameter-two setting, discard the constant suffix and apply the two extremal-set bounds above to the remaining coordinates. ∎

The quantizer's nonzero cell margin and *common* fixed point are substantive hypotheses. A linear threshold passing through the fixed point may have `delta=0`, in which case contraction alone gives no finite innovation horizon. A recurrent model with input-dependent attractors does not satisfy the common-fixed-point premise.

## Theorem 3: true-state collisions versus observation collisions

For deterministic recurrent `F`, if `F^t(x)=F^t(y)` at some visit, then `F^(t+s)(x)=F^(t+s)(y)` for every `s>=0`. Any downstream tied or untied probe produces identical future readouts. In contrast, `q(F^t(x))=q(F^t(y))` says only that **one quantized reading** collided; later visits can separate those states while the hidden trajectories remain distinct.

The general collision persistence lemma is proved in `MathCan/TemporalCutCapacity.lean` using induction, with the kernel axiom inventory printed by CI.

## Relationship to COE-01/02/03 and limitations

COE-01 establishes exact task-relative chromatic binary width. COE-02 adds an `ell_1` cut budget and a diameter-two anticode obstruction. COE-03 shows low-precision binary heads can need many more coordinates than bounded-range fractional heads. This note moves the discrete coordinates into **time**, where a tied recurrent map can expose complementary cuts. The mathematical equivalence is conditional on allowing a phase-carrying latent state; learned models may have inadequate time diversification or may forget earlier distinctions.

This result concerns a specified finite evaluator, exact binary readouts and aggregate Hamming constraints. It is independent of the infinite-dimensional source results [OpenAI Math #098](https://github.com/openai/math/blob/main/lean/docs/098.md) and [#332](https://github.com/openai/math/blob/main/preprints/Metric-Markov-Cotype-Two-of-l1-October-5-2026/README.md); those papers motivated the distinction between full metric fidelity and stable forward observation. No infinite-dimensional theorem from those sources is imported as an axiom.

## Theorem 4: ordered versus commutative readout histories

Some recurrent probes gain from the number of threshold crossings while contributing no distinguishability through the order in which those crossings occurred. Suppose an observer emits a symbol from an alphabet of size `q=2^k` on each of `T` visits, but its decoder sees only the *unordered multiset* of outputs. The number of possible distinguishable multisets is exactly

`M(T,k) = binom(T+2^k-1, 2^k-1)`.

This follows by stars-and-bars: each histogram is a nonnegative integer vector of `q` bin counts with total `T`. By comparison, the ordered transcript alphabet contains `2^(kT)` sequences. If `n>M(T,k)`, every commutative decoder must collide on some evaluator states, regardless of the recurrence.

For one bit per tick this specializes to `M(T,1)=T+1`, because only the count of ones remains. More sharply, when the evaluator is `K_n`, the largest number of its edges that any decoder with `B` distinct output categories can distinguish is

`binom(n,2) - [r binom(a+1,2) + (B-r) binom(a,2)]`,

where `a=floor(n/B)`, `r=n mod B`. **Proof:** group the `n` states by their observed category. Every within-group pair collides. If two groups differ in size by at least two, moving one member from the larger to the smaller group strictly reduces the number of colliding pairs. Thus the minimum number of collisions occurs for balanced group sizes, giving the formula. ∎

At `n=8,T=4,k=1`, count-only observation permits at most five distinct class codes and can separate at most `25/28` evaluator pairs per context. These counting limits hold without an `ell_1` diameter constraint. The separate diameter-two bounds in Theorem 1 can strengthen them. The observed frozen checkpoint experiment tests whether order *actually contributes* to task distinctions, rather than assuming that a four-step history uses all `2^4` possible ordered words.

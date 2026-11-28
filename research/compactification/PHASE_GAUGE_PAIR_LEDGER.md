# COE-07: exact pairwise information ledger for clock-gauge quotients

**Status:** new elementary synthesis for the Compactification / LoopScope research program. Proof below. Literature-wide novelty or priority unassessed. Source motivation is OpenAI Math #098 (global metric compression obstructions) and #332 (forward Lipschitz extension), together with the completed COE-05/06 binary recurrent coding investigations. No deep claims from those manuscripts enter the proof.

## Finite complete-evaluator theorem

Let \(x_1,\ldots,x_n\) be n evaluator-distinct states. A fixed shared binary recurrent readout produces one T-bit word \(W_i\) per state. Define its cyclic necklace \(N_i = \min_{0\le s<T}\mathrm{rot}_s(W_i)\) and count \(C_i=\mathrm{popcount}(W_i)\). Treat the initial observation time as an unknown gauge element in \(\mathbb Z/T\mathbb Z\).

For any finite descriptor \(Q\), let \(n_q\) be the size of its preimage among the n labels and put

\[
  D(Q) := \#\{i<j:Q_i\ne Q_j\} = {n\choose2}-\sum_q {n_q\choose2}.
\]

**Theorem COE-07A (exact phase-gauge pair ledger).** The numbers of distinguished pairs satisfy

\[
D(W)\ge D(N)\ge D(C),\qquad
\boxed{D(W)-D(C)=[D(W)-D(N)]+[D(N)-D(C)]}.
\]

The two brackets are individually nonnegative. The first counts distinctions requiring the starting phase. The second counts distinctions invariant to cyclic phase shifts but invisible to a histogram of positive observations. With \(m_w\) labels giving ordered word w, \(m_\nu\) giving necklace \(\nu\), and \(m_c\) giving count c, the terms are exactly

\[
D(W)-D(N)=\sum_\nu {m_\nu\choose2}-\sum_w {m_w\choose2},
\quad D(N)-D(C)=\sum_c {m_c\choose2}-\sum_\nu {m_\nu\choose2}.
\]

*Proof.* A pair is distinguished by Q exactly when its two descriptors differ. The only undistinguished pairs lie within the preimages of individual descriptors, giving the counting formula. Every necklace has constant Hamming weight, so count is a function of necklace; necklace is a function of ordered word. Their partitions are therefore nested. Subtract the collision formula twice. All terms are finite integers, including cases with empty classes. \(\square\)

**Theorem COE-07B (sharp one-weight necklace capacity).** Suppose all n labels have the same observed count \(w\) across \(T\) visits, and let \(q(T,w)\) denote the number of length-T binary necklaces of weight w. Put \(q=\min(q(T,w),n)\), \(a=\lfloor n/q\rfloor\) and \(r=n\bmod q\) (assume n≥1 and 0≤w≤T). The maximum phase-invariant number of distinguished pairs obtainable with these constraints is

\[
 \boxed{D(N)_{\max}={n\choose2}-(q-r){a\choose2}-r{a+1\choose2}.}
\]

The maximum can be attained by assigning the n states as evenly as possible to q distinct necklaces, using r classes of size a+1 and q−r classes of size a. Since all words have the same weight, \(D(C)=0\). When q≥n, every pair is distinguished; if q=1, the bound is zero.

*Proof.* For a fixed number of used necklace classes, the number of collision pairs is \(\sum_i\binom{n_i}2\). For two group sizes u≥v+2, changing them to u−1 and v+1 decreases collisions by u−v−1>0. Therefore a collision-minimizing allocation has group sizes differing by at most one. Increasing the number of used classes weakly decreases collisions, until all min(q(T,w),n) slots are used. The quotient/remainder expression follows. Each distinct necklace exists by the definition of q(T,w); assigning those representatives constructs the optimal observer. \(\square\)

For T=8 and w=4, the exact necklace count is 10. Thus for n≤10, eight recurrent observations support **n(n−1)/2** clock-gauge-invariant distinctions even with identical positive counts, absent margin or decoder constraints. COE-06's one-flip-correcting construction imposes additional inter-orbit distance and therefore a stricter coding problem.

**Theorem COE-07C (class-merge gap).** If two code classes containing a and b labels become equivalent under a coarser observation, then exactly ab distinctions are lost. More generally, any quotient sequence can be priced by summing these pairwise merge costs, independently of the order of merging.

*Proof.* \(\binom{a+b}{2}-\binom a2-\binom b2=ab\). For several merges apply the identity inductively; both the final partition and original partition determine the overall difference in collisions. \(\square\)

## Exact native output-telemetry diagnostic

An independent read of the earlier committed `LoopedTransformers` 7M pretrained `gaoxin492/step_21700` correctness-receipt (checkpoint SHA-256 `932b5e0d...`) and matched benchmark counted 1,795 eligible distinct-digit pairs within the 64-item `S4_stalled` stratum. At eight ACT visits, the source has \(D(W)=1414\), \(D(N)=1389\), \(D(C)=1369\). Thus COE-07A attributes **25** distinctions to known clock phase and **20** further distinctions to cyclic-invariant order. The other three strata have no cyclic-invariant gain over count in that eight-visit source record.

The same frozen output trace has the following **visit-budget sensitivity** for stalled boards, with the identical 1,795 eligible pairs:

| Visits | Ordered D(W) | Cyclic D(N) | Count D(C) | Clock-sensitive | Cyclic beyond count |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 1,278 | 1,244 | 1,244 | 34 | 0 |
| 8 | 1,414 | 1,389 | 1,369 | 25 | 20 |
| 16 | 1,447 | 1,428 | 1,422 | 19 | 6 |

These are descriptive post-hoc replays across the same frozen boards, and all outcomes are recorded with answer-aware correctness bits.

This empirical descriptor is \(W_t=1\{\text{model's target-cell prediction at step t equals the known target}\}\). It uses **ground truth**, so it is an oracle on an existing native run, rather than a deployable model-observable probe or evidence of a learned dark-fiber code. The preregistered native latent-probe test in `LoopedTransformers PR #72` requires checkpoint inference and its independently frozen fit/test gate. The source file Git blob IDs appear in that PR's `NATIVE_OUTPUT_TELEMETRY.md`.

## Formalization boundary

`MathCan/PhaseGaugePairLedger.lean` checks the group-merge identity \(\binom{a+b}2=\binom a2+\binom b2+ab\) for arbitrary natural sizes using a recursive pair-count definition, the general nested-collision ledger given its order premises, and concrete arithmetic cells. It prints the transitive axiom set for each statement. The combinatorial partition proof and sharp balanced necklace-capacity theorem are proved in this manuscript; full formalization of those higher-level constructions remains an open step.

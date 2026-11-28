# COE-08: exact permutation null for observable separation under unknown labels

**Date:** 2026-11-15. **Research status:** elementary new application and an exact second-moment identity for evaluator-graph observers. No literature-wide originality claim. The underlying graph and combinatorial identities stand independently of OpenAI Math #098 and #332; those manuscripts motivate the task-relative metric/extension program begun in COE-01.

## Problem and crucial epistemic boundary

An evaluator may declare two states `distinguished` when their histories differ. In COE-07 the history at time `t` was **truth-conditioned correctness**, `C_t(i)=1{prediction_t(i)=ground_truth(i)}`. Ground truth is required to compute this history, so it is an **oracle diagnostic**, not a probe available to an online monitor. Pair separation alone can be large when histories contain zero information about the evaluator labels.

Fix `N>=4` positions with evaluator labels `l_i`. Write `M=#{i<j : l_i != l_j}`. Fix a multiset of histories `W={w_1,...,w_N}`. A descriptor `q` maps histories to a finite set of classes. Let `n_a` count members of descriptor class `a`. Randomly assign the entire histories to labelled positions by a uniform permutation `pi`, preserving the label multiset and the history multiset. Define

`D_q(pi) = #{i<j : l_i != l_j, q(w_{pi(i)}) != q(w_{pi(j)})}`.

**Theorem COE-08.1 (exact conditional mean).**

`E_pi D_q = M * (N^2 - sum_a n_a^2) / (N*(N-1))`.

If `fine` determines `coarse` (for example ordered -> cyclic -> dihedral -> Hamming weight), then

`E_pi [D_fine-D_coarse] = M * (sum_b n_coarse,b^2 - sum_a n_fine,a^2) / (N*(N-1))`.

The latter is nonnegative. It measures **histogram refinement under a label-independence null**, independently of how many target labels the history predicts.

*Proof.* For every eligible labelled pair `i<j`, its two distinct randomly assigned histories are uniform among the `N(N-1)` ordered, distinct-index pairs. There are `sum_a n_a(n_a-1)` ordered pairs of histories with identical descriptor. Thus the probability of distinction is `1-sum_a n_a(n_a-1)/(N(N-1)) = (N^2-sum_a n_a^2)/(N(N-1))`. Sum indicators over the `M` eligible labelled pairs. For nested descriptors, subtract their expectations. QED.

## Exact conditional variance including overlapping pairs

The refinement difference can be viewed as an edge-crossing count on a fixed **source trace graph** `H`, whose vertices are the `N` original histories and whose edges join pairs `a,b` with `coarse(w_a)=coarse(w_b)` and `fine(w_a)!=fine(w_b)`. Let `e=|E(H)|`, `A=sum_v binom(deg_H(v),2)` (unordered pairs of edges meeting at one vertex), and `B=binom(e,2)-A` (unordered disjoint edge pairs).

For label multiplicities `m_c`, put `(x)_k=x(x-1)...(x-k+1)` with `(x)_k=0` when `x<k`, and define:

- `p = 1 - sum_c (m_c)_2/(N)_2`.
- `p_adj = sum_c m_c (N-m_c)_2/(N)_3`.
- `p_dis = 1 - 2 sum_c (m_c)_2/(N)_2 + [sum_c (m_c)_4 + sum_{c != d}(m_c)_2 (m_d)_2]/(N)_4`.

**Theorem COE-08.2 (exact second moment under the conditional permutation null).** The refinement gain `G(pi)=D_fine(pi)-D_coarse(pi)` obeys

`E G = e*p`,

`Var(G) = e*p + 2*A*p_adj + 2*B*p_dis - (e*p)^2`.

*Proof.* For a fixed edge of `H`, its endpoints receive different target labels with probability `p`. For two edges sharing a vertex, condition on the common vertex label `c`. Both other labels must differ from `c`; the probability, summed over `c`, is `p_adj`. For disjoint edges, inclusion-exclusion over the event that each pair has equal labels yields `p_dis`. Expand `G^2` into diagonal terms plus twice the sum over unordered edge pairs, separated into the `A` adjacent and `B` disjoint possibilities. QED.

The variance formula retains dependence between evaluator pairs sharing states; treating pair indicators as independent would produce unjustifiably narrow confidence intervals.

## Native pretrained S4, pinned finite application

From `MoralityLabAI/LoopedTransformers` `mechinterp/loopscope02/results/benchmark_bundle.json` Git blob `01ec63b4...` and `trm_results.json` Git blob `3c35daeb...`, original checkpoint SHA256 `932b5e0d...`. The S4 stratum contains `N=64` Sudoku boards with label histogram `[10,8,2,5,8,7,6,10,8]`; it has `M=1795` unequal-digit pairs. Source histories are correctness bits, and all of these statistics remain **truth-conditioned**.

| Window | Count-class square sum | Dihedral-class square sum | Trace-graph edges | Observed gain | Exact shuffled-label expectation | Exact variance |
|---|---:|---:|---:|---:|---:|---:|
| T=4 | 1308 | 1308 | 0 | 0 | 0 | 0 |
| T=8 | 1020 | 978 | 21 | 20 | 1795/96 = 18.6979 | 11285015/5809152 = 1.94263 |
| T=16 | 904 | 888 | 8 | 6 | 1795/252 = 7.12302 | 46069057/60043032 = 0.767267 |

A 10,000-permutation deterministic shuffle of the **existing full histories** gives at `T=8` a one-sided upper-tail plus-one p-value `0.3148`, with central empirical interval `15..21` and mean `18.7114`. At `T=16`, the upper-tail p-value is `0.9580` and central interval `5..8`. This is a post-hoc exploratory negative control, not a preregistered hypothesis test, and the single checkpoint/board cohort limits inference to the case examined.

## Stronger sanity check: a fully label-blind predictor

Suppose each step produces an independent uniform random digit from `K` possible labels, independently of the true label. Each correctness bit is then iid Bernoulli(`1/K`) even conditional on the label, so the entire correctness history is statistically independent of that label. Nevertheless, the probability that **two independent correctness histories differ as ordered words** equals

`1 - ((1-1/K)^2 + (1/K)^2)^T`.

For `K=9,T=8` this is approximately `0.8280` (about 82.8% distinct pairs), despite zero information about the target label. This is a mathematical counterexample to interpreting distinct correctness histories as evidence of a useful probe.

## Reproduction and scope

The companion standard-library implementation `mechinterp/phase_gauge07/label_shuffle_null.py` implements both exact formulas, a deterministic fixed-multiset shuffle, and SHA-pinned source replay. Its tests include all 3-point binary-labelled configurations of width 3, exact 4-point second-moment checks against independent permutation enumeration, and pinned S4 cells.

`MathCan/ObserverPermutationNull.lean` certifies the finite integers and histogram moment identities. The general expectation/variance theorems are proved above and are **not** claimed as Lean-kernel theorems.

Next scientific gate: extract pretrained residual activations, fit candidate probes strictly on the registered `S1+S3` train split, evaluate `S2+S4` with label-free binary histories, and use a group-preserving label shuffle computed *after* probe freeze. Include a matched scalar/output-logit probe and an intervention on the selected activation subspace. This can distinguish descriptive compression from causally important phase codes.

# COE-06: exact clock-gauge capacity for a single tied recurrent bit

**Date:** 2026-11-15. **Scope:** proved finite metric/coding lemmas, an exact standard-library exhaustive bound for all lengths at most 13, a length-14 constructive witness, and frozen-head post-hoc replay. **Novelty:** research-program formulation and integration; priority over coding-theory literature has not been established. No inference on an externally pretrained recurrent transformer is claimed.

Companion applied implementation: `MoralityLabAI/Compactification-Theory/research/chromatic_observer_gym_v1/gauge_orbit_codes.py` and `resource_bound.py`. This continues COE-05's phase-gauge question using the same physical idea of one readout reused at every tick. The relevant motivating source manuscripts are OpenAI Math family [098](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/098.md) (limitations of bi-Lipschitz compression) and [332](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Metric-Markov-Cotype-Two-of-l1-October-5-2026/README.md) (Lipschitz extension). The theorems below are elementary finite arguments and **do not require** either manuscript's deep claims.

## 1. Quotient decoding theorem

Let `C={c_1,...,c_n}` be binary words of length `T`. Their cyclic rotation group is `G=C_T`. A decoder sees `g.c_i ⊕ e`, where the phase `g∈G` is arbitrary and the adversarial Hamming error `e` satisfies `|e|≤t`. The decoder knows the word length and codebook, but not `g` or `i`.

Define the **inter-orbit distance**

\[
\Delta([u],[v]) := \min_{g,h\in G} d_H(g.u,h.v)
                      = \min_{h\in G}d_H(u,h.v).
\]

The second equality uses the fact that coordinate rotations preserve Hamming distance. Distances inside the same orbit are irrelevant because all of its members represent the same label.

**Theorem PB-1 (exact gauge-robust decoding condition).** Every label can be decoded uniquely for every phase and every pattern of at most `t` corrupted bits if and only if `Δ([c_i],[c_j])≥2t+1` for all distinct labels `i,j`.

*Proof.* Under the inequality, an observation within radius `t` of one label orbit cannot also be within radius `t` of another, by the triangle inequality. Nearest-orbit decoding is unambiguous. Conversely, if distinct label orbits have words at distance `d≤2t`, partition their `d` differing positions into two sets of sizes at most `t`. Flipping one set from the first word yields an observation within `t` flips of the second word. Both labels could have produced that observation, so guaranteed recovery is impossible. ∎

When all codewords have the same Hamming weight, distances are even. Thus for a single flipped bit (`t=1`), the condition is equivalent to `Δ≥4`.

## 2. Deletion-necklace packing theorem

Identify weight-`w` words with `w`-element subsets of the cyclic index set `Z/TZ`. A **necklace** `[S]` consists of all cyclic translates of `S`. For a representative `S` define its *deletion resources*

\[
 R(S)=\{\,[S\setminus\{x\}]:x\in S\,\},
\]

where the brackets denote cyclic equivalence of `(w−1)`-subsets. Let `N(T,w−1)` be the total number of such necklaces, computable by enumerating the `\binom{T}{w-1}` binary masks and keeping one representative per orbit.

**Theorem PB-2 (disjoint deletion-necklace resources).** For a constant-weight code with inter-orbit distance at least four, the resource sets `R(S_i)` for distinct labels are pairwise disjoint. Consequently,

\[
\boxed{\sum_{i=1}^n |R(S_i)|\le N(T,w-1).}
\]

*Proof.* Suppose `[S_i\setminus\{x\}] = [S_j\setminus\{y\}]`. After a cyclic translate, the two `w`-subsets share `w−1` positions. They are identical (which places them in the same orbit), or differ in exactly two binary coordinates. Either case contradicts distinct labels with orbit distance at least four. The sets of necklace resources are therefore disjoint; counting all of them gives the inequality. ∎

The same argument applies to complements, exchanging weights `w` and `T−w`. For a **computable upper bound**, enumerate all candidate weight-`w` necklaces and sort their resource costs `r_1≤r_2≤...`. Any `n` selected labels use at least `r_1+...+r_n` resources. Therefore `n` is at most the largest `m` whose first `m` costs sum to at most `N(T,w−1)`. Taking the minimum with the complement bound strengthens the certificate. This is an exact finite counting argument that uses integer arithmetic, with no reliance on solver optimality.

## 3. Sharp fourteen-tick witness for twenty-one labels

**Theorem PB-3 (optimal time width within the stated model).** A time-independent cyclic register and one fixed single-bit readout can encode **21 labels in 14 visits** with a constant activity count across labels and correct every single bit error despite arbitrary unknown cyclic phase. Under these same constant-weight and adversarial one-bit correction conditions, **13 or fewer visits cannot encode 21 labels**.

*Upper construction.* Take a fourteen-bit state. At each visit apply the same transition `R(s)=rotate_right_14(s)` and read the least-significant bit. The codewords below are initial states (decimal), all of weight six:

```
207 243 311 473 543 629 697 811 851 903 1133
1175 1337 1351 1419 1445 1587 1677 1865 2451 2709
```

These are distinct cyclic necklace representatives. The independent exact oracle checks the distance from each of the 21 words to *every rotation* of each other word: the minimum cross-orbit distance is four. Theorem PB-1 provides one-flip correction. To make the witness fully reproducible, the oracle additionally tests each possible cyclic phase and each of the fourteen single-bit corruptions, plus the clean case. Five label orbits have length seven and sixteen have length fourteen; the total tested predictions are `5·7·15 + 16·14·15 = 3885`, all correct. The tied shift/readout outputs the original codeword when the first tick is aligned, and a rotation otherwise. Because every label has six positive readings, an activity-count observer distinguishes zero of the `binom(21,2)=210` evaluator pairs. ∎

*Lower obstruction.* The exact integer deletion-resource bound from PB-2 is evaluated for every integer `1≤T≤13` and every weight `0≤w≤T` (complement symmetry reduces to `w≤floor(T/2)`). The maximal resource-count bounds over weights are:

| Maximum visits `T` | 8 | 9 | 10 | 11 | 12 | 13 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Maximum labels allowed by resource bound | 3 | 3 | 5 | 7 | 14 | 17 |

All smaller `T` have still smaller bounds. The worst case is `T=13,w=6`. There are exactly `99` deletion-necklace resources; among the `132` candidate six-subset necklaces, six use five resources and the remaining 126 use six. Selecting 18 would consume at least `6·5 + 12·6=102>99` resources. Hence at most 17 labels fit at that width. At `T=12,w=6`, the cost multiplicities `(cost,number)` are `(1,1),(2,1),(3,3),(5,4),(6,71)`, totaling 66 resource classes, and the corresponding bound is 14. The checked-in `COE06_BOUND_LEDGER.json` contains the full per-width and per-weight enumeration, recomputed by `resource_bound.py` using only the standard library. Thus all `T≤13` exclude 21 labels; the length-14 construction is optimal for the stated requirement. ∎

These bounds concern **constant Hamming weight** (identical positive counts), a *single tied head* with access to the exact cyclic register state, unknown start phase, and guaranteed correction of one arbitrary bit flip. Variable-weight or phase-marked observers are separate classes.

## 4. Heldout phase-gauge diagnostic on COE-05

A second, observational analysis replays the previously selected frozen one-bit heads (synthetic causal-attention models 2411–2413, contexts 4–7) and replaces each four-bit transcript with its **canonical cyclic necklace**. The replay fixes the COE-05 fit-only thresholds and weights, checks original source checkpoint identifiers, and independently recomputes every evaluated edge from stored per-visit activations.

| Readout on 336 heldout evaluator pairs | Separated |
| --- | ---: |
| Aligned ordered transcript | 243 |
| Rotation-invariant necklace | 233 |
| Positive-count-only | 233 |
| Differences preserved by order but destroyed by unknown phase | 10 |

All ten COE-05 order-only hits vanish in the unknown-phase quotient. This was not a new prospective study: it is an exact post-hoc diagnostic on the same frozen observations, with no probe retraining. The constructed twenty-one-label register is a proof of possible *phase-invariant* capacity, and is **not** the trained attention model.

## 5. Evidence scope

- `gauge_orbit_codes.py`: exact cross-orbit distances, all corruption cases, explicit tied register map.
- `resource_bound.py`: exhaustive integer enumeration for every `T≤13` and weight; independent of SciPy or any external MILP solver.
- `phase_gauge_replay.py`: frozen, read-only COE-05 heldout replay with the original fit-only heads.
- `MathCan/PhaseBlindObservers.lean`: 21 finite words, constant-weight and pairwise rotated-margin certificates, and the exact largest subcritical integer-budget consequences under Lean 4.35.0. The resource-disjointness theorem and all-`T` enumeration remain supported by the written proof and exact Python oracle, rather than a complete Lean formalization.

This mathematical campaign concerns synthetic models and a coding-theoretic capacity theorem. A native-pretrained LoopedTransformers experiment should extract raw per-visit activations for pinned checkpoints, lock evaluator edges before fitting probes, and compare aligned/unknown-phase accuracy and causal task behavior on group-disjoint holdouts.

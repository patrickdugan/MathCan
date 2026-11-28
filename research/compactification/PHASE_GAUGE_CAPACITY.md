# COE-05: constant-weight phase capacity, error correction, and clock gauge

**Research date:** 2026-11-15. **Status:** proved finite and general propositions, independently executable exact witnesses, finite Lean certificates. The affine-hyperplane code is the classical Steiner quadruple system `S(3,4,8)`/extended Hamming code construction. This note claims the **temporal-observer application and research-program formulation**, not literature-wide priority for the underlying combinatorial facts.

## Source relationship and restrictions

The program began with OpenAI Math #098 (finite-dimensional bi-Lipschitz embedding obstructions) and #332 (Lipschitz extension to `l1`). The present phase coding arguments use elementary finite combinatorics, so they do not depend on the correctness of those source manuscripts. Earlier COE-01..04 identify observer width, cut-metric budgets, output precision, and recurrent history bandwidth. This theorem asks what information survives forgetting *when* the recurrent probe fired.

A state index `a` has a binary transcript `c(a)=(c_0(a),...,c_(T-1)(a))`. A one-head recurrent observer uses one readout map `p` on every visit of a *time-homogeneous* state transition `R`: `c_t(a)=p(R^t(x_a))`. The full-word observer sees `c(a)`. The histogram observer sees only the Hamming weight `|c(a)|`. An unknown, uniformly random clock phase acts by cyclic shifts of `c(a)`.

## 1. Constant-weight observer capacity

**Theorem PG-1 (phase information in a constant-count stratum).** For any `0 <= w <= T`, the maximum number of labels separable using `T` one-bit observations *with every transcript of weight exactly w* is `binom(T,w)`. Any observer restricted to the activation count merges all these labels. All `binom(T,w)` words can be realized by one time-independent cyclic-shift transition on an initial `T`-bit register and one fixed bit-zero readout.

*Proof.* There are exactly `binom(T,w)` subsets of `T` positions having size `w`. A full-history decoder needs distinct subsets for distinct labels. Conversely, embed each label as its chosen subset's incidence vector in a `T`-bit register. Let `R` be cyclic right rotation, and let `p` read the lowest bit. For `t=0,...,T-1`, the successive readouts are precisely the original register bits in order. The readout has identical weights on every visit and requires no label-conditioned phase lookup. Every count equals `w`. This proves both the upper bound and its attainability. `∎`

For general binary histories with at most `s` switches between successive visits, their number is exactly

`M(T,s) = 2 * sum_{j=0}^{s} binom(T-1,j)` for `0 <= s <= T-1`.

The first bit has two choices, and choosing exactly `j` of the `T-1` boundaries at which to switch determines the entire history. Thus small transition budgets can limit available phase codes even when the history has `2^T` unconstrained possibilities.

## 2. Exact single-flip-robust, count-blind family

Represent the eight coordinates by the points of `F_2^3`. For each nonzero `a in F_2^3` and `b in F_2`, let

`H_(a,b) = { x in F_2^3 : a dot x = b }`,

and let its characteristic word be `c_(a,b) in {0,1}^8`. There are `7*2=14` such words. Every hyperplane has four points, so `|c_(a,b)|=4`. Distinct parallel hyperplanes are complements, hence distance eight. Two nonparallel affine hyperplanes intersect in exactly two points, hence their words are distance four. Therefore the minimum distance of this 14-word code is **four**.

**Theorem PG-2 (sharp eight-visit robust phase code).** There exists a single-head, tied, time-homogeneous eight-visit recurrent observer that distinguishes `14` labels; all histories have count four, and nearest-code decoding corrects every single flipped observation. Eight visits are the minimum possible for any fourteen-label, constant-count, one-flip-correcting binary-history observer.

*Proof.* The construction above has pairwise distance at least four. Any word within Hamming distance one of a codeword is uniquely closest to that codeword because the distance between different codewords is at least four. PG-1 supplies the cyclic shift implementation. The count-only evaluator has a single output category.

For optimality, a binary constant-weight code correcting a single arbitrary bit flip has pairwise Hamming distance at least three; since all codewords have the same weight, Hamming distances are even, so the minimum is at least four. For `2 <= w <= T-2`, consider all `(w-1)`-subsets contained in the support of each codeword. Two different supports cannot share one, or their distance would be two. Each weight-`w` codeword owns `w` distinct `(w-1)`-subsets. Counting yields

`n*w <= binom(T,w-1)`.

Applying the same argument to complements gives

`n*(T-w) <= binom(T,T-w-1)`.

For `w=0,T` only one word exists; for `w=1,T-1`, every pair of distinct words is distance two, so at most one label is allowed. With `T=7`, the preceding bounds imply at most three labels when `w=2,5` and at most seven when `w=3,4`, so *any constant-weight single-flip-correcting code of length seven contains at most seven words*. Padding a shorter code with zeros reduces it to that case. Thus fourteen labels require `T>=8`. For `T=8,w=4`, triple counting gives `n <= binom(8,3)/4 = 56/4=14`, achieved by the fourteen affine hyperplanes. `∎`

The 14 supports form the classical Steiner quadruple system `S(3,4,8)`: each three-point subset of `F_2^3` lies in exactly one affine plane. The exact implementation in `Compactification-Theory/research/chromatic_observer_gym_v1/phase_register.py` checks all 56 unique triples, all 91 pairwise distances, every transcript, and all 112 single-flip decodes.

## 3. Unknown phase is an information quotient

Let a finite group `G` act on transcripts, and suppose the unknown nuisance transformation `g` is drawn uniformly from `G` independently of the label. The receiver observes `g.c(a)`. Let `O` denote the set of different `G`-orbits represented by the `n` codewords.

**Theorem PG-3 (uniform phase-gauge Bayes bound).** With uniformly distributed labels and a noiseless uniformly random unknown `g`, optimal full-transcript decoding accuracy is exactly `|O|/n`. If `G` is the cyclic shift group and all codewords have weight `w`, the number of available orbits (binary necklaces) equals

`N(T,w) = (1/T) * sum_{s=0}^{T-1} [T/gcd(T,s) divides w] * binom(gcd(T,s), w/(T/gcd(T,s)))`.

*Proof.* For a fixed orbit, uniform transformation gives a uniform output distribution across all its elements. Indeed, each orbit member has exactly `|G|/|orbit|` preimages in `G`. Hence labels in the same orbit produce identical observations, and labels in distinct orbits give disjoint supports. With a uniform prior, the best decoder succeeds for exactly one label per represented orbit, yielding `|O|/n`. For cyclic shifts, a word fixed by shift `s` is constant on each of its `gcd(T,s)` cycles, each of length `T/gcd(T,s)`; its weight must be a multiple of that length. Burnside's lemma averages fixed-word counts over the `T` shifts, yielding the displayed formula. `∎`

At `T=8,w=4`, `N(8,4)=(70+2+6+2)/8=10`. The selected fourteen hyperplane words occupy exactly **four** cyclic orbits, of multiplicities `[2,4,4,4]`. Without a shared phase origin their optimal error-free label accuracy becomes `4/14=2/7` under uniform independent phase shifts; full clock alignment restores `14/14`. The count-only decoder has optimal accuracy `1/14` for these labels. This is a precise clock-gauge obstruction; neither training-time random permutations nor fixed global order reversal are equivalent to uniformly unknown independent phase shifts.

## 4. Verification boundaries

The Lean file `MathCan/PhaseGaugeCapacity.lean` checks the exact 14-word witness: the printed codebook, constant weight, pairwise distance at least four, its tied-shift readout identity, and integer packing counts. The general theorems PG-1..PG-3 have the complete written proofs above; Lean does not certify the infinite family or Burnside's lemma. The original manuscript pair #098 and #332 is motivation only, and no priority over established error-correcting codes is claimed.

The applied COE-05 experiment uses independent frozen four-visit causal-attention models to measure the *presence or absence* of order-only distinctions. Those learned models are not the constructive eight-visit cyclic-register system, and trained large-pretrained-model evidence remains a separate requirement.

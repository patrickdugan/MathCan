# COE-03: the precision–time trichotomy for task-relative observers

**15 November 2026. Status:** self-contained mathematical derivation, exact finite rational certificates, an exploratory synthetic training pilot, and small Lean kernel witnesses. Literature-wide originality is unassessed. No assertion of original OpenAI manuscript proof verification or trained-language-model capability.

## Motivation and provenance

Continue [COE-01](CHROMATIC_OBSERVER_THEOREM.md) and [COE-02](CHROMATIC_CUT_CAPACITY.md). Their source pair is OpenAI's September–October 2026 Math [family 098](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/098.md), on the limitations of bi-Lipschitz dimension reduction, and [family 332](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Metric-Markov-Cotype-Two-of-l1-October-5-2026/README.md), on the extension of Hilbert-subset Lipschitz maps to ℓ1. The theorems below use elementary finite coding, packing, Hoeffding's inequality, and coordinatewise McShane extension; the statements of families 098 and 332 are motivation rather than assumed lemmas.

We seek an output code `f:X→[0,1]^k` on `n` equilateral states, with `d_X(u,v)=1` for `u≠v`, such that every evaluator pair is distinguished by an ℓ1 output margin of at least 1 and output Lipschitz budget at most 2:

```
            1 <= ||f(u)-f(v)||_1 <= 2         (u != v).
```

This is a complete evaluator graph `K_n`. We distinguish *numeric coordinates*, their *precision*, and *time steps*, rather than counting every numeric coordinate as a single Boolean bit.

## COE-03.1: binary, continuous, and temporal capacity

**Theorem (three resource regimes).** For every integer `n>=5`:

1. A one-shot binary observer `f:X→{0,1}^k` has the displayed ℓ1 margin and budget **if and only if** `k>=n-1`. The construction uses `0,e_1,...,e_(n-1)`; any surplus coordinates may be set to zero.
2. The minimum width of a one-shot *real-valued* observer with the displayed margin and budget is `Theta(log n)` as `n→∞`. In particular, if the integer `k>=3` satisfies `k>18 ln(n(n-1))`, there is a code in `{0,3/k}^k` with every pair's ℓ1 distance in `[1,2]`. Any such finite code extends to every ambient metric space containing X as a function into `[0,3/k]^k` with **global ℓ1 Lipschitz constant at most 3**, independently of n and k.
3. Suppose a deterministic recurrent observer emits `w` Boolean coordinates per time step for T steps. Its evaluator receives the **entire concatenated transcript**, and the *total* ℓ1 distance between every pair of transcripts must remain in `[1,2]`. Then `wT>=n-1` is necessary and sufficient. A time-multiplexed one-hot code attains `T=ceil((n-1)/w)`, provided the latent state remains accessible at each step. The lower bound applies even when later Boolean outputs are chosen adaptively from earlier outputs.

**Binary proof.** Let `C⊂{0,1}^k` have `1<=d_H(x,y)<=2` for all distinct members. XOR-translate a member to 0. All remaining words have Hamming weight 1 or 2. Write T for the singleton supports and F for the two-element supports. Any two members of F intersect; each member of T must belong to every member of F. If `|T|=1`, all pairs in F are incident to its element, giving `|C|<=1+1+(k-1)=k+1`. If `|T|>=2`, there is at most one member of F, and when `|T|>=3` there are none, again giving at most k+1. If T is empty, any pairwise-intersecting family of 2-subsets is either a star of size at most k-1 or (if it has no common element) a subset of the three edges of a triangle. For `k>=3`, `|C|<=1+max(k-1,3)<=k+1`. If F is empty then `|C|<=1+k`. Widths `k<=2` can encode at most four states outright; for `n>=5` the bound follows. One zero word plus the k unit words achieves n=k+1.

**Real-valued upper bound.** Independently choose k fair bits for each of n states. A fixed pair's Hamming distance `D` is `Binomial(k,1/2)`. Hoeffding gives

```
Pr[D <= k/3 or D >= 2k/3] <= 2 exp(-k/18).
```

The union bound over `n(n-1)/2` pairs gives failure probability at most `n(n-1) exp(-k/18)<1` under the stated strict k inequality. Therefore some assignment satisfies `k/3 <= D <= 2k/3` for all pairs. Scale the 1 entries by `a=3/k`: every ℓ1 pair distance `aD` lies in `[1,2]`. On the equilateral finite set, each scalar coordinate is a-Lipschitz. The clipped McShane extension

```
F_j(z) = clip_[0,a] min_(u in X) {f_j(u)+a*d(z,u)}
```

agrees with the finite data and is globally a-Lipschitz. Sum over k scalar coordinates: `||F(z)-F(z')||_1 <= ka*d(z,z')=3*d(z,z')`. The finite observer itself has Lipschitz constant at most 2, with an explicit ambient extension of constant at most 3. This is a constructive, specialized extension and requires no appeal to source family 332.

**Real-valued lower bound.** Choose a center among the n output points. Every point lies in its ℓ1 radius-2 ball. The open ℓ1 balls of radius 1/2 centered at the n outputs are pairwise disjoint in k-dimensional space, and all lie inside an ℓ1 ball of radius 5/2 around the center. By scaling Lebesgue volume, `n(1/2)^k <= (5/2)^k`, so `n<=5^k` and `k>=log_5 n`. Together with the probabilistic construction, minimal real coordinate width is `Theta(log n)`. This lower bound allows *any* real output amplitudes in `[0,1]`, not merely the two-level construction.

**Temporal proof.** Concatenation turns any deterministic `w`-coordinate, T-step transcript (including adaptive policies) into a length-`wT` binary word. Its aggregate ℓ1 distance equals the Hamming distance of the flattened word. The binary bound above yields `n<=wT+1`. For sufficiency, assign a distinct one-hot bit to each of n-1 states, assign 0 to the remaining state, and partition the bit positions into T successive blocks of width w. The resulting full transcripts have distances 1 or 2. The proof assumes externally available repeated state access and full-transcript evaluation; it makes no claim about the internal recurrent state memory required to implement this schedule.

## COE-03.2: finite-grid precision is asymptotically necessary

Let the observer values lie on the uniform `b`-bit grid `G_q={0,1/q,...,1}`, where `q=2^b-1` and `b>=1`.

**Theorem (precision upper and lower bounds).** For every n>=5 there exists a `b`-bit-grid observer satisfying the pair-distance conditions with

```
       k > 50 ln(n(n-1)),
       q = 2^b-1 >= 2k,
       b = ceil(log2(2k+1)) = O(log log n),
       k = O(log n).
```

It has an ambient global ℓ1 Lipschitz extension of constant at most 3. Conversely, for any such grid observer, regardless of its construction,

```
                  n <= (1+kq)^(2q).             (†)
```

Consequently, if `k<=C ln n` for a fixed constant C as n grows, its precision must satisfy `b=Omega(log log n)`. Thus **the smallest asymptotic grid precision among logarithmic-width observers is Theta(log log n)**, with the upper and lower bounds proved here under the margin-one/budget-two assumptions.

**Upper-bound proof.** Choose independent fair bits as above but use deviations `k/10` instead of `k/6`. With `k>50 ln(n(n-1))`, positive probability remains that every pair has `2k/5 <= D <= 3k/5`. Set

```
             A = ceil(5q/(2k)),       a = A/q.
```

Since `q>=2k`, `5/(2k)<=a<=5/(2k)+1/q<=3/k`. All pair distances satisfy `1 <= a D <= 9/5`; coordinate values are in `G_q`, and clipped coordinatewise McShane extension gives global Lipschitz constant `ka<=3`.

**Lower-bound proof.** Multiply each grid codeword by q to get an integer vector in `{0,...,q}^k`. Fix any state 0. As all distances from it are at most 2, each other vector differs from it in at most `2q` coordinates, because a changed integer coordinate contributes at least 1 to the sum of absolute differences. Encode a vector by its sorted list of modified `(coordinate, new value)` pairs, padded to length `2q` with a sentinel. There are at most `kq` possible modifications (each coordinate has at most q alternatives), plus the sentinel. This encoding is injective, giving (†). If `k<=C ln n` and `q<=ln n`, then

```
  ln n <= 2q ln(1+kq) <= 2q ln(1+C(ln n)^2),
```

so `q >= ln n/[2 ln(1+C(ln n)^2)] = Omega(ln n/ln ln n)`. For `q>ln n` the same asymptotic lower bound holds. Taking `b=log2(q+1)` yields `b>=log2(ln n)-O(log2 ln ln n)`, hence `b=Omega(log log n)`. The probabilistic construction completes the matching order claim.

**Interpretation.** Width and precision impose different geometric constraints on a quantized probe. A 10-bit *numeric* feature counts as ten stored bits if fully materialized. The theorem is about width as a count of observed scalar coordinates, conditional on their value alphabet and ℓ1 budget; it does not say the total bit budget `kb` is asymptotically smaller than a binary code's bit budget.

## COE-03.3: finite exact and trained synthetic cells

**Exact K5 soft certificate.** Code the five states in three channels as

```
  (0,0,0), (1,0,0), (0,1,0), (0,0,1), (1/3,1/3,1/3).
```

The ten pair distances are 1, 4/3, or 2. No three-bit binary observer can achieve the same full `K5` margin and cap; the binary anticode theorem requires four channels. All 64 independent coordinatewise threshold-pattern combinations for this particular soft certificate fail either separation or the distance cap. The MathCan Lean module checks the exact numerator arithmetic and its finite threshold statement; the general asymptotic proofs remain in this manuscript.

**Reproducible n=1024 finite grid.** Choose `n=1024`, `k=256`, pseudo-random seed 2305, Python `random.Random(seed).getrandbits(k)` for each state, and amplitude `a=12/1023=4/341`, corresponding to ten-bit grid levels. The independently replayed integer Hamming extrema are `91` and `168` across all 523,776 pairs. Therefore every output distance is in `[364/341,672/341]`, a subset of `[1,2]`. Coordinatewise extension gives global ℓ1 Lipschitz bound `k*a=1024/341<4`. The fixed SHA-256 digest (which includes the parameters and all word bytes) is `2a99809deb1babd57d9d10e959775429470fafa90d390331b6d82f6f581dd5eb`. The n=1024 sample is an **exact finite certificate**, separate from the existence bound's worst-case sufficient constants. Thresholding at 1/2 sends every small-amplitude coordinate to zero. Thresholding below a preserves the original high-Hamming words and violates the total ℓ1 cap of 2.

**CPU training pilot.** A linear three-output probe on five fixed one-hot states is trained with projected subgradient descent, learning rate 0.45, maximum 4,000 steps, deterministic seeds 0 through 9. Each pairwise loss is squared hinge distance outside `[1,2]`. Stopping loss is below `1e-12`, with evaluation tolerance `1e-3`. When all ten edges train, 10/10 seeds meet the soft constraint; binarizing all coordinates at 1/2 yields 0/10 full-K5 valid codes. With exploratory holdout edges `(0,4),(1,3),(2,4)`, all ten fit the seven training pairs, and 2/10 satisfy the three withheld pairs. This split was considered during exploratory analysis and is **not a preregistered generalization claim**. All reported cases are synthetic and trained in the CPU sandbox; no language model, SAE checkpoint, mechanistic intervention, or real validation cohort was used.

## Next research gate

Extract deterministic frozen activation states from a named looped-transformer checkpoint. Define evaluator edges using intervention outcomes before selecting or tuning probes. Quantize features at fixed output scales and compare (i) edge coverage (ii) Lipschitz usage (iii) numerical precision (iv) aggregation horizon. Evaluate under a held-out task split, and report actual storage bits and runtime separately from observer width. The current source is a mathematical reference and proof-audited controlled experiment; deployment and model-capability claims are outside scope.

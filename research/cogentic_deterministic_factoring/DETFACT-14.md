# DETFACT-14: static minimal-arena scheduling on a fresh suite

Status: descriptive feasibility PASS; static 16-bit speed target PASS; workload bootstrap includes parity. Synthetic modular execution only; no claim of efficient relation generation or proof of the original Cogentic complexity theorem.

## Design

Use the unchanged DETFACT-12 arena worker and six-action grid from DETFACT-13. The prior DETFACT-13 fitted weights are frozen, with no new fit. Compare certified minimum (minimum arena, breaking ties by widest chunk), static16 (32 odd slots, 16-bit chunks), and the prior structural scheduler. All six actions have segment size at least 32; the arena formula is independent of chunk width. Consequently action 0 (32,16) and action 1 (32,64) are exactly equal in arena size and attain the grid minimum. If action 0 does not fit, no grid action fits. This is a corollary of the abstract DETFACT13Arena minimum-completeness theorem, not a new Lean theorem.

Fresh seed 1402, 12 workloads, independently shuffled balanced levels: K=24576/40960/65536; target modulus widths 160/384/640 (actual 159–640); batches 2/5/10; supplied exponent widths 128/384/896. Six caps 512/768/1024/1536/3072/8192 bytes. Three shuffled native timing repeats per action. All policy decisions and the primary/secondary gates were frozen before native timing. This is a local prospective freeze, not independent timestamped preregistration.

For every workload-action pair, execute all three repeats under the exact required arena cap, compare residues and first proper gcd results to independent Python exact arithmetic, and cross-check all four operation counters against the structural profile. Run one additional cap-minus-one rejection per workload-action. Thus every feasible selected configuration is tested under its tightest possible cap; any looser cap is justified by the unchanged preflight condition. No additional separate run is made for each workload-cap-policy combination. Runtime ratios reuse these shared action dispatch measurements, add separately measured selector medians (31 warm samples), and use workload-cluster bootstrap (3000 resamples). Cold cost includes clearing the profile/prime caches and selecting an action (three samples). Python dispatch includes subprocess launch, native execution and JSON parse. Kernel time is recorded separately. The parent Python memory, unbounded structural-profile caches, stack, libc and allocator overhead are outside the worker arena cap. Timings and bootstrap are descriptive on a small synthetic suite.

## Mathematical observation: singleton prime-power regime

For a prime p<=K, its maximal power q=p^a<=K satisfies q>sqrt(K): either p>sqrt(K), so q>=p>sqrt(K), or p<=sqrt(K), so pq>K implies q>K/p>=sqrt(K). For K>=65536 every q has bit length at least 9. The worker's conservative chunk-packing condition rejects any two such powers within a 16-bit chunk, because their bit-length sum is at least 18. A power wider than 16 bits is executed directly. Thus static16 performs one modular power per odd prime power at K>=65536 (regardless of segmentation), plus the supplied odd exponent per base. This statement concerns this implementation's conservative packing rule, not a guarantee of runtime optimality. At K=65536 the measured 6541 odd prime powers yield b*(6541+1) power calls on all four fixtures (12 runs). Combining factors can change binary exponentiation multiplication counts in either direction; no universal speed optimality follows.

## Results

216 exact-cap grid invocations; 1224 residues and 1224 first-split results matched Python; 216 tuples of four operation counters matched; all 72 cap-minus-one invocations rejected with zero allocated bytes. All 47 grid-feasible pairs completed for each policy, 25 infeasible pairs correctly abstained, zero over-cap allocations. The supplied exponents are synthetic; the common p-1 annihilation promise is not assumed.

| policy | grid-best hits | geometric mean grid ratio | warm selector µs | cold selector µs |
|---|---:|---:|---:|---:|
| certified minimum | 9 | 1.033304 | 3.025 | 3.025 |
| static16 | 26 | 1.014588 | 0.351 | 0.351 |
| frozen structural cost | 31 | 1.011149 | 8.0175 | 8466.007 |

Relative to certified minimum, static16 warm dispatch ratio 0.981887 (kernel 0.984596), workload bootstrap 95% interval [0.961223,1.004785]; descriptive 1% threshold passed, interval includes parity. Frozen structural cost warm ratio 0.978559 (kernel 0.982379), interval [0.958595,1.001744], cold ratio 1.208261. Static16 and structural cost agree on 42/47 feasible choices; static/cost ratio 1.003401 warm, 0.812645 cold. Static16 is a practical cache-free default for this worker and grid; neither a statistically established universal speed gain nor a claim of optimality. Static16 was faster on 9/12 workload-level comparisons, slower on three; repeated caps are clustered rather than independent observations.

## Replay

The full archive includes exact tested sources, prior cost_frozen.json, protocol, frozen choices, all per-workload measurements, final receipt and hashes. With GCC, Python, NumPy and SciPy, run in a clean copy containing arena_audit.c, arena_bench.py, cost_audit.py, cost_frozen.json and static_audit.py:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python static_audit.py freeze
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python static_audit.py measure 0 12
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python static_audit.py finish

The measure range is half-open and can be subdivided. The Git summary includes original hashes. A variable shadowing error in the initial finish stage caused a KeyError when counting repeats; corrected solely in the receipt-generation line, then recomputed the summary from the saved grid and unchanged frozen choices (selector timings remeasured). No post-test tuning or changes to the measured worker. The original prior-weight receipt is supplied in the archive. The formal model still covers abstract arena accounting only; C memory safety, actual relation producer, upstream paper proof and full complexity theorem remain separate obligations.

Next: use the static policy as a baseline for any further resource scheduling experiments. Prioritize formal streamed exponent semantics and the original factoring relation-production audit before extending the scheduler further.

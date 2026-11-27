# DETFACT-10: budget-conditioned native execution scheduling

Status: executed synthetic CPU experiment. Allocation and arithmetic checks pass; learned superiority over the fixed per-budget baseline fails descriptively on this suite. This is an execution-policy experiment, not a factoring complexity proof or a demonstration of efficient relation production.

## Design

Run OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python policy_audit.py with Python, NumPy, scikit-learn, GCC and GMP development libraries. The script builds the existing DETFACT-09 native worker with -O3 and strict compiler warnings. It compares eight explicit/stream configurations under six tracked live-payload caps (1024, 2048, 4096, 16384, 65536, 262144 bytes). Batch count is a workload requirement, not an action. No retry is allowed.

Synthetic odd composite inputs are products of random odd integers. Supplied positive Mstar is generated independently of the modulus; the common p-1 exponent promise is not assumed. The independent Python reference constructs the exact exponent via a full sieve and explicit product and computes modular residues and first proper gcd results. All native output hashes match it. 36 workloads, eight configurations, three shuffled execution repeats: 864 uncapped native benchmark runs, 2,808 native base residue/split comparisons against 117 independently computed Python base results. Three repeats estimate a median, with limited timing precision.

Train: 18 workloads, K=8192/32768/98304, actual modulus bit lengths 59–160, Mstar bits 32/96/256, batch sizes 1 and 4. Calibration: 6 workloads, K=12288/49152/114688, modulus lengths 71–191, Mstar bits 48/128/384, batch sizes 3 and 5. Held-out: 12 workloads, K=16384/65536/131072, modulus lengths 79–224, Mstar bits 64/160/512, batch sizes 2 and 6. The generator's indexing does not reach the third configured batch value in any split (8, 10, 12). This limits coverage and must be repaired for a prospective new suite; retain these results as executed.

For each configuration fit two log-target ridge regressions (alpha=.5) on log2(K, modulus bits, batch, Mstar bits). Multiply predicted payload by 1.05 times the maximum of 1 and the calibration observed/predicted ratio. This is an empirical margin, not a safety theorem. Choose fastest predicted feasible action, falling back to minimum predicted adjusted payload if none qualifies. Hard native cap enforces the actual requested live-payload budget.

Baseline: for each cap choose a single configuration on training data, lexicographically minimizing avoidable budget failures, then mean log regret to the training grid oracle, then action ID. Smallest baseline always chooses (128,64). Freeze models, margins, fixed policy, and all held-out actions in a JSON file before collecting held-out performance. This is a same-process prospective split, not an externally time-stamped preregistration.

## Results

| policy | feasible success | unavoidable aborts | geometric mean regret ratio | max ratio | grid-best hits |
|---|---:|---:|---:|---:|---:|
| learned | 67/67 | 5 | 1.035107 | 1.234585 | 35 |
| fixed | 67/67 | 5 | 1.013172 | 1.293239 | 46 |
| smallest | 67/67 | 5 | 1.215331 | 1.435382 | 7 |

72 workload-cap pairs per policy; five of these have no feasible measured grid action. All 216 policy decisions were validated via 157 distinct capped invocations (identical workload-cap-action requests are deduplicated). No avoidable budget aborts. Capped results agree with uncapped feasibility and independent reference output. Regret ratios use the uncapped median runtime of the selected configuration divided by the fastest feasible grid median, not the timing of the capped rerun. Learned faster than fixed in 4 cases, tied in 42, slower in 21; paired geometric mean ratio 1.0216497568. Smaller observed maximum regret does not establish a minimax advantage. Workloads repeat across caps, so 67 pairs are not independent observations. No significance claim. Fixed action (2048,1024) was chosen at 4 KiB and every larger cap; (512,256) at 2 KiB; (128,64) at 1 KiB.

Conclusion: retain fixed policy as the operational baseline; do not promote ridge controller. The experiment is a descriptive negative result for average-regret superiority. A further prospectively frozen experiment should cover all batch sizes, model timing residuals against the fixed baseline, allow abstention to that baseline, and hold out larger K, different modulus families and longer exponents. Include actual end-to-end policy inference and capped execution time, workload-level uncertainty and warm/cold process comparisons. This is a potential resource scheduling gym only after showing a learned advantage.

## Reproduction and receipt

policy_audit.py regenerates the full policy_receipt.json and frozen_policy.json. Timing varies across runs. policy_summary.json records the actual run's summary and SHA-256 of its full receipt, frozen policy and source. The full original receipts and logs are in the companion replay archive provided separately, not committed here. RSS is process high-water, not a clean workspace measurement (held-out 160100–160740 KiB); native cap excludes untracked allocator and stack overhead as in DETFACT-09. The original Cogentic PDF, effective coverage proof, relation producer and Lean verification remain outstanding.

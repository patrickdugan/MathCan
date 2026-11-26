# DETFACT-11: residual scheduler with abstention

Status: executed synthetic CPU experiment; primary performance gate FAIL. The fixed per-capacity policy remains the operational baseline. This experiment concerns verified execution of supplied exponents and does not establish the upstream factoring complexity claim or relation production.

## Protocol

Run in a clean copy of this directory, with Python, NumPy, scikit-learn, GCC and GMP development libraries. Set OPENBLAS_NUM_THREADS=1 and OMP_NUM_THREADS=1. Execute these phases in order:

    python residual_audit.py init
    python residual_audit.py train 0 12
    python residual_audit.py cal 0 6
    python residual_audit.py freeze
    python residual_audit.py test 0 12
    python residual_audit.py capped 0 72
    python residual_audit.py finish

Ranges are half-open and may be subdivided. The script uses unchanged native_audit.c and policy_audit.py from DETFACT-09/10. The protocol file was created before training, and the frozen policy and decisions were written before any held-out measurements; this is a local phase freeze, not external preregistration. The full original files and receipt are in the replay archive; residual_summary.json records their hashes.

The workload generator independently shuffles balanced level lists, asserts every configured level occurs, and uses disjoint seeds and workload dimensions. Training 12 cases, K in {8192,32768,98304}, batch {1,4,8}, modulus 71–256 bits; calibration 6, K in {12288,49152,114688}, batch {3,6,10}, modulus 87–319 bits; test 12, K in {24576,81920,147456}, batch {2,7,16}, modulus 111–448 bits and supplied exponent {96,256,768} bits. Every level occurs. Some test cases use uneven factor sizes. Moduli are synthetic products of random odd integers, and supplied exponents are not assumed to satisfy the common p-1 promise.

Actions and caps are the unchanged DETFACT-10 eight-action grid and six caps. For each action, fit a log-payload ridge model on log2(K,modulus bits,batch,exponent bits); the upper prediction adds the maximum positive calibration error and log(1.05). For every ordered distinct action pair fit the log ratio of their median uncapped dispatch wall times using ridge alpha=1, and subtract the maximum positive calibration overprediction. The default is the fixed per-cap action selected only on training data using the DETFACT-10 objective with wall time substituted for native time. The controller departs for speed only if its calibrated lower predicted log gain exceeds log(1.02) and the candidate is predicted feasible. If the default is predicted infeasible, use the smallest adjusted predicted payload, preferring predicted feasible candidates. No retries. Calibration margins are empirical, not guaranteed memory envelopes.

Preselected descriptive gate: no additional avoidable budget failures and geometric mean paired capped dispatch ratio <=0.99. Workload bootstrap accounts for repeated caps within workload. Measure three shuffled uncapped repeats per action, then three fresh capped repeats per distinct selected action/case. When policies choose the same action they share the capped measurements; this pairing controls shared execution noise but is not two independent runs. Include the median of 31 warm selector timing samples in the capped median dispatch time. Dispatch includes subprocess launch, native execution, and output parse; inference excludes Python startup, imports, and offline training. Regret uses the uncapped grid wall-time median and the selector median; it is a different metric from capped end-to-end comparison.

## Results

720 grid runs, 4,560 native base residue and first-split comparisons against the exact independent Python reference, all passed. 225 capped worker invocations, including budget aborts; successful capped output hashes match the independent reference. Aggregating over caps, both policies completed 62 of 63 grid-feasible cases, with nine grid-infeasible cases and one avoidable failure. Fixed geometric mean grid ratio 1.0148014, worst 1.1004737; residual 1.0158421, worst 1.1006973. Median warm selector times 0.11 and 8.5075 microseconds. Paired capped ratio 0.9987376654, workload bootstrap 95% interval [0.9937896932,1.0012224290], 62 joint successes across 12 workloads. Primary gate fails; the small descriptive improvement is below 1%. All three speed switches occurred on a single workload (test-07, K=24576, 447-bit modulus, batch 16, exponent 96 bits), at 16,384/65,536/262,144 byte caps. Each chose explicit instead of the fixed 2048-byte/1024-bit streaming action. Actual capped wall ratios 0.940645, 0.962303, 0.968920, while the uncapped grid preferred the fixed action in all three decisions. This difference suggests timing noise; repeated caps on one workload are not independent wins. Other 59 joint successes use the same action and pay additional selector overhead. The controller abstained 58 times and returned predicted_no_feasible 11 times; these 11 decisions did not change the action.

## Posthoc diagnostic, separate from frozen evaluation

Both policies failed test-07 at the 2048-byte cap, selecting action 3 (512-byte segment, 256-bit chunk). The measured full tracked payload was 2104 bytes versus an adjusted model prediction of approximately 1528 bytes. Action 1 (128-byte segment, 64-bit chunk) was independently feasible. A new retrospective capped replay succeeded with 1717 bytes and matched the original arithmetic hash. This establishes that the hard cap prevented an unsafe allocation and a smaller configuration can recover the known missed case. It does not establish held-out superiority of a modified policy.

## Next experiment

DETFACT-12: deterministic allocation-aware scheduling. Replace learned memory feasibility with a conservative, independently audited bound for native tracked payload; when a cap cannot be certified, use a minimal certified configuration or return unresolved. Benchmark the fallback in a fresh frozen suite before attempting a learned speed policy again. Include a policy that uses certified feasibility only, and another that compares safe candidate configurations with the fixed default. A tracked-payload bound still excludes stack scratch, allocator overhead and the Python parent process; a full-process RAM claim needs separate verification. Use actual allocator enforcement and matched native arithmetic. The Cogentic PDF, Lean companion and effective relation-production argument remain outstanding.

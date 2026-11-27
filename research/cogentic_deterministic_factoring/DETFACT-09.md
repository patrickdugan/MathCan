# DETFACT-09: native GMP allocator-budgeted execution

Status: native synthetic CPU replay completed. This extends DETFACT-07/08's exact execution interface; it is not the upstream relation-production algorithm.

## Method

Run `python native_bench.py` in this directory with GCC and GMP development libraries on a 64-bit Linux system. The script builds C with -O3 -std=c11 -Wall -Wextra -Werror and launches isolated worker processes. GMP 6.3.0, GCC 14.2.0, Python 3.13.5 were used in the execution container (AMD EPYC 9V74). The same segmented sieve supplies both the explicit balanced-product baseline and streamed chunk paths. Inputs are synthetic. Timing includes initialization, sieve, exponent construction and residue evaluation; it excludes split and JSON output. Full-run tracked peak includes those later phases.

Allocation hooks charge requested live payload bytes for GMP alloc/realloc/free and explicit sieve/residue-array allocations. A budget of zero disables the cap. A nonzero budget causes controlled process exit code 3 before a request that would exceed it. This is a cap on logical requested live payload, not total transient heap memory (realloc may temporarily retain both blocks), stack allocations, GMP stack scratch, allocator metadata, loader overhead or process RSS. Zero-length malloc requests can occupy one uncounted byte. All successful tests cleared tracked allocations. The worker accepts a bounded K, segment and chunk width, and explicit positive Mstar. It is a toy research runner, not a hardened parser. Native checkpoint persistence/authentication is not implemented; the stream flushes at segment boundaries. DETFACT-08 covers checkpoint semantics.

For each base the worker emits the initial odd-exponent residue, followed by the first proper gcd's squaring index and divisor (or null; -1 denotes a direct base gcd). Equality of s and initial residue proves the entire deterministic chain agrees, though the receipt directly compares only initial residues and first split results. Independent Python math.lcm, modular pow and gcd checks cover 312 native fixtures, 2496 residues and 2496 split results. Two invalid-domain controls and one enforced budget rejection passed.

## Timed sweep

Stress inputs: N=1000000007*1000000009 and Mstar=2^9*3^5*5*7*11. These inputs are not assumed to satisfy the upstream p-1 promise. Four bases, three repetitions, same modular output and first-split hashes within each K. A balanced explicit product is the baseline, not the slower incremental lcm algorithm. The native_receipt.json records all 24 configurations, 72 timed repeats, exact counts and hashes. It is reconstructed from the measured rows; the replay script regenerates a fresh receipt. No cryptographic-scale factoring speed claim.

| K | Mode | Segment B | Width bits | Median ms | Peak tracked B |
|---:|---|---:|---:|---:|---:|
| 65536 | explicit |8192|256|3.008|23808|
| 65536 | stream |2048|256|3.142|2656|
| 65536 | stream |8192|256|2.954|8800|
| 262144 | explicit |8192|256|16.796|153920|
| 262144 | stream |2048|256|12.366|3000|
| 262144 | stream |8192|1024|11.312|9240|
| 1048576 | explicit |8192|256|55.095|1072312|
| 1048576 | stream |512|64|57.012|2545|
| 1048576 | stream |512|256|46.337|2545|
| 1048576 | stream |2048|256|48.361|3600|
| 1048576 | stream |8192|256|47.513|9744|
| 1048576 | stream |8192|1024|46.609|9840|

At the largest K the 512-byte/256-bit streaming configuration has 421.3x smaller tracked payload and 15.9% less median evaluation time than the baseline. This is a retrospective best-grid comparison, not a frozen policy result. Peak RSS was uniformly 96268 KiB in the subprocess harness (possibly inherited process high water), so RSS does not establish a whole-process memory reduction. The explicit odd exponent was 1512562 bits; the best streaming config used at most 256-bit operands. This sweep uses one fixed 60-bit modulus, small batch sizes and only three repeats. Timing noise is visible; no cross-hardware or large-modulus generalization claimed.

## Frozen policy

Select the fastest median configuration feasible under the tracked cap on K=65536 only, tie by payload then lexicographic mode/span/width. Write the calibration receipt before evaluating K=262144 and 1048576. The 4096-byte policy picks (2048,256), the 16384-byte policy picks (8192,256). Both meet their enforced caps on both held-out K. Ratios to the best feasible tested configuration on holdout are respectively 1.000/1.044 and 1.078/1.025. This is a small fixed-grid policy transfer, not a learned adaptive controller or independently time-stamped preregistration.

At K=262144, explicit/512-byte stream/8192-byte stream medians in ms for batch 1: 5.233/3.519/3.471; for batch 16: 46.373/45.632/42.832. The batch comparisons are matched on bases and arithmetic result, not identical low-level operation counts (GMP selects its own powering algorithms). All modes use shared enumeration, so this does not isolate enumeration reuse versus an unbatched baseline.

## Next gate

DETFACT-10: train or fit a budget-aware selection policy with disjoint moduli, K, batch and exponent-size families. Compare with fixed policies and grid oracle under enforced payload caps; report regret and unresolved results. Measure full-process memory in a clean native launcher, include stack and allocator effects, and separately validate authenticated checkpoints. Actual upstream PDF, effective relation coverage, efficient relation production and Lean compilation remain unresolved.

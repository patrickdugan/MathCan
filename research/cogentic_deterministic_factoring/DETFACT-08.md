# DETFACT-08: segmented enumeration, shared bases and checkpointed exponent execution

Status: independent exact execution audit on synthetic moduli, local CPU Python 3.13.5 measurements. No relation producer, upstream factoring complexity proof, or Lean kernel proof.

## Method and invariant

Enumerate odd primes in increasing order using a byte per odd integer in each segment. Sieve the primes up to floor(sqrt(K)) once. For each odd base prime p mark odd multiples beginning at max(p^2, first odd multiple in the segment), stepping by 2p. Any composite odd integer <=K has an odd prime divisor <=sqrt(K); starting at p^2 therefore marks every composite without striking p itself. Generate q=p^floor(log_p K) by exact integer multiplication and division comparisons. The odd saturation exponent is the product of all these q times odd(Mstar). Use the same segmented enumerator for both the explicit balanced carry product baseline and the streaming path.

A batch of bases shares the stream: after each completed prime-power prefix the vector contains a_i raised to odd(Mstar) times the product of that prefix, modulo N. Modular power composition holds also for nonunits. A chunk is flushed before its conservative width bound would exceed W; a single prime power wider than W is processed separately. The actual maximum exponent operand width is bounded by max(W,bitlen(K),bitlen(odd(Mstar))). Streaming never constructs the full exponent. Compute the two-adic count separately as 1+v2(Mstar)+floor(log2 K); DETFACT-07 proves equivalence of the subsequent fixed-order split trace. This experiment checks initial residues, not a new factoring run.

## Workspace and work accounting

Sieve payload counts the maximum of the base sieve plus packed base-prime array, or the packed prime array plus one segment of S bytes. Array capacity, headers, temporary objects, integer allocator overhead and arithmetic scratch are excluded. On this implementation the packed base primes occupy eight bytes each; residue and exponent payload depend on log N, W, log K, and the explicitly supplied Mstar. The general sieve work has the usual marking count O(K log log K) plus scanning overhead from iterating over base primes for every segment, approximately O(ceil(K/(2S))*pi(sqrt(K))); the receipt counts actual segment marking writes, excluding base-sieve initialization. One batch shares the prime enumeration; modular powering still scales with batch size. This is not a comparison against independently enumerating each base.

Checkpoint at a segment boundary after flushing the pending chunk. Bind the parameters, next segment index and residue vector to a SHA-256 checksum. Correct trusted state can resume exactly by the prefix invariant. An unkeyed checksum is not authentication or a proof of valid prefix execution. The test deliberately recomputes the digest on a forged residue, which passes the structural checker; independent prefix replay detects the forgery. The prototype is for internally generated integer inputs and trusted local checkpoints, not a hardened external parser or succinct proof system.

## Actual CPU experiment

Run python segmented_audit.py on Linux. It launches fresh Python subprocesses per timed trial. Fixed synthetic N=1000000007*1000000009, Mstar=2^9*3^5*5*7*11 and bases 2,3,4,5. Two K values, four configurations, three repeats each. Time is median elapsed seconds inside the worker (excluding process startup); RSS is maximum reported ru_maxrss in KiB across repeats. Explicit construction uses a binary-carry balanced product over the same sieve rather than repeatedly computing the huge lcm. Check the independent math.lcm reference in 1,344 small residue comparisons. All configuration result hashes match at each K. Stress cases measure exponent evaluation, not relation discovery or splitting; the supplied Mstar need not meet the factoring promise.

| K | mode | segment bytes | chunk bits | median ms | sieve payload bytes | max exponent bits |
|---:|---|---:|---:|---:|---:|---:|
| 16384 | explicit | 8192 | n/a | 11.074 | 8431 | 23675 |
| 16384 | stream | 512 | 64 | 11.759 | 752 | 64 |
| 16384 | stream | 8192 | 256 | 10.743 | 8431 | 256 |
| 16384 | stream | 16384 | 256 | 10.818 | 8431 | 256 |
| 65536 | explicit | 8192 | n/a | 38.971 | 8616 | 94449 |
| 65536 | stream | 512 | 64 | 49.438 | 936 | 64 |
| 65536 | stream | 8192 | 256 | 40.717 | 8616 | 256 |
| 65536 | stream | 16384 | 256 | 40.206 | 16808 | 256 |

All workers reported exactly 96280 KiB peak RSS; this shared high-water figure cannot resolve the small algorithmic allocation differences (and may reflect inherited process high water). No measured RSS reduction is claimed. The payload count shows 936 bytes for sieve storage at the smallest tested segment, excluding the exponent, residues and Python overhead. The 64-bit streamed path replaces a 94449-bit operand with at most 64 bits, about 1476x smaller in operand width, at approximately 27% higher measured time. The 256-bit/8192 configuration is about 4.5% slower at K=65536, with the same sieve payload as the baseline. Larger segment 16384 is a slightly faster streaming configuration in this tiny sweep, but the sample is too small to claim a stable tuning advantage. The original planned sweep to K=1048576 timed out without a complete receipt; the actual run was reduced to K=16384 and 65536. The receipt records all completed timed repeats, not extrapolations. No GPU or user desktop run.

## Next gate

DETFACT-09: an isolated native GMP or Rust worker with allocator-level telemetry, explicit byte budgets and larger K sweeps. Compare batch sizes and adaptive chunk policies at matched arithmetic work; register memory/time Pareto criteria in advance. Add authenticated checkpoint envelopes or exact prefix replay when crossing trust boundaries. Validate the full split trace with the new enumerator. Upstream PDF, effective relation coverage and the actual arithmetic producer remain unresolved. Lean formalization is pending.

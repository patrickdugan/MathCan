# DETFACT-12: exact fixed-arena feasibility

Status: primary descriptive feasibility gate PASS. Synthetic execution experiment for supplied saturation exponents, not an audit of Cogentic's relation-production theorem. The C implementation is independently derived and finite-tested, not Lean verified.

## Workspace theorem

For canonical nonzero hexadecimal input lengths n_l,e_l, put L=ceil(n_l/8), E=ceil(e_l/8), r=floor(sqrt(K)), and c=min(S,floor((K-1)/2)). These are also the limb counts obtained from the true bit lengths. With b bases, the worker requests a single zero-initialized allocation of A=4*((b+8)*L+E+2)+r+1+c bytes. Six L-limb arrays hold N, a reserved Montgomery one, the power base, a normal residue and two gcd operands; the Montgomery product/reduction scratch uses 2L+2 limbs, bL limbs hold the residues, E limbs hold the supplied exponent, and the final r+1+c bytes hold the base and segment sieves. All explicit arrays are slices of this allocation. The chunk and loop counters are scalar uint64_t variables. Under K,S<=10000000, 1<=W<=64, 1<=b<=128 and at most 1024 hex digits per input, the size arithmetic fits 32-bit size_t (maximum below 6 MB). The worker compares A with a nonzero cap before calloc; if A exceeds it, the worker returns unresolved with zero arena allocation. If A fits and allocation succeeds, the same arena suffices throughout evaluation and splitting. This is a source-level explicit-arena accounting proof, not a proof of all C semantics or an upper bound on stack, libc I/O, allocator metadata, process RSS, argv or the Python parent. Allocation failure remains possible.

## Arithmetic invariant

Use radix beta=2^32, R=beta^L and odd N<R. For a,b in [0,N), the schoolbook scratch initially holds T=ab<R^2. Every inner multiply-add fits uint64_t since (beta-1)^2+2(beta-1)=beta^2-1. The reduction loop uses q_i=T_i*(-N_0^{-1}) mod beta to cancel the i-th low limb, with carry propagation. The resulting exact integer is T+NQ with 0<=Q<R, divisible by R. Since ab<N^2<NR, its quotient is below 2N; one conditional subtraction produces the canonical residue, congruent to ab R^{-1} mod N. Two extra scratch limbs cover carries. A repeated-doubling initialization computes aR mod N; Montgomery powers preserve this representation, including for nonunits. Conversion back multiplies by ordinary 1. Binary gcd uses fixed-width subtraction and shifts; its modulus operand begins odd. The sieve visits each odd prime <=K once and computes its maximal power <=K. Each flushed chunk has width <=W; if a single prime power exceeds W, process it directly (it still fits uint64_t by the K bound). Thus the initial residues and two-adic count agree with DETFACT-07's explicit reference, and the first proper gcd in each base's split trace agrees. No assumption that the supplied Mstar annihilates all prime-factor groups is made for these tests. A missing split is an allowed result.

## Replay

Run in a clean directory with GCC and Python 3:

    python arena_bench.py train
    python arena_bench.py test
    python arena_bench.py finish

The protocol is written before training and ranks and decisions are frozen before test measurements; this is a local phase freeze, not independently timestamped preregistration. Twelve training and fifteen held-out synthetic workloads use disjoint K/batch/modulus/exponent levels, every configured level occurs. Held-out moduli 95–448 bits, batch 2/6/12, exponent 64/192/512 bits, K 768/3072/8192. Six configurations and seven budgets from 256 to 8192 bytes; three shuffled uncapped timing repeats. Fixed selects the best training-ranked action per cap (failures first, then log regret). Certified ranked uses the same ranking restricted to exact feasible actions. Certified minimum minimizes arena size, breaking ties by larger chunk width then action id. Both abstain when the feasible set is empty. 486 grid invocations and 176 actual capped invocations (deduplicated by case/action). Capped successes match independent Python math.lcm, pow and gcd output hashes. Regret uses uncapped median dispatch wall time relative to the fastest feasible grid action; it excludes scheduler inference cost, uses only successful feasible cases, and is descriptive rather than a paired speed superiority test.

| policy | feasible completed | avoidable failures | preflight abstentions | geometric mean regret ratio |
|---|---:|---:|---:|---:|
| fixed | 78/80 | 2 | 0 | 1.06764944 |
| certified ranked | 80/80 | 0 | 25 | 1.06605578 |
| certified minimum | 80/80 | 0 | 25 | 1.05323323 |

All policies have zero over-cap allocations; the fixed worker rejects 27 requests including 25 grid-infeasible. Both certified policies recover test-04 and test-11 at the 768-byte cap with 692 and 680-byte arenas. 2736 grid residue and first-split comparisons, 1600 edge residue and first-split comparisons, 640 exact-cap and cap-minus-one tests, five invalid-input controls passed. Additional GCC UBSan run on 144 independently generated fixtures passed 432 residue and 432 first-split comparisons with zero reported UB. UBSan does not prove memory safety. RSS was 96908–97420 KiB in the subprocess harness; no whole-process RAM claim. Results are for a new standalone worker; no matched speed comparison against GMP. Absolute timings are hardware-specific and grid choices may change on replay. Full original logs, receipts and tested sources are packaged separately. The Git summary records hashes of the original receipt and frozen protocol.

## Next gate

DETFACT-13: isolate the arena feasibility calculation in Lean and test source-level memory bounds with a dedicated memory-safety verifier; then add cost-aware scheduling over certified actions and compare against certified minimum on fresh larger K and modulus families. Treat measured time regret as the objective only after feasibility, and include scheduler inference costs. Formal kernel checking, upstream PDF, effective analytic coverage and efficient relation production remain pending.

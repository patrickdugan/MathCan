# DETFACT-07: streamed saturation exponent and exact split semantics

Status: independently derived streamed execution theorem and exact finite replay. No new relation producer, asymptotic factoring proof, kernel-checked Lean proof, or cryptographic-scale performance claim.

Inputs are the certified relation lcm Mstar>0 and uniform subgroup-index cap K>=1 from DETFACT-02/06. The reference implementation constructs S=lcm(1,...,K) explicitly. We seek to avoid that large integer during execution.

## 1. Exact decomposition

By unique factorization S=product_{p prime <=K} p^floor(log_p K). Define odd(x)=x/2^v2(x). Then

    M = 2 Mstar S
    s = 1+v2(Mstar)+floor(log_2 K)
    u = odd(Mstar) product_{3<=p<=K, p prime} p^floor(log_p K)
    M = 2^s u.

Here log floors are computed by exact integer comparisons, not floating point. K=1 gives an empty product. Each prime power q is computed by repeated multiplication subject to q<=K/p. Each is bounded by K. A positive odd chunk product may group consecutive prime powers without changing u.

For any residue a and modulus N>=2, (a^x mod N)^y mod N = a^(xy) mod N for nonnegative integer x,y. Induction over the factor stream gives exact a^u mod N, including for nonunits. Once the initial residue and s agree, the sequence of squarings and gcds in DETFACT-01 agrees term for term, and the first returned proper divisor agrees for a fixed base ordering. This execution equivalence is independent of whether the exponent actually satisfies the p-1 promise; that promise still depends on the original verified relation bank and cap.

## 2. Memory versus work ledger

The reference binary exponentiation must represent the full odd exponent u. Its bit length is log_2(u)+O(1), on the order of K+bitlen(Mstar) in the worst case for large K (the Chebyshev function is Theta(K)). Streaming holds a single modular residue and an integer prime power, using trial division with O(log K) bits of counters and no stored prime list. The prototype uses an explicit Mstar, and its odd part is processed separately. It does not eliminate that input cost.

For chunk width W, an online conservative packing rule flushes if the sum of the bit lengths of the current chunk and next prime power exceeds W. A prime power exceeding W is processed individually. Thus the maximum exponent operand width is at most max(bitlen(odd(Mstar)),W,bitlen(K)). BigInt modular products also need O(bitlen(N)) bits. The binary exponentiation implementation uses a string representation of each current exponent, whose length obeys the same bound. Actual memory includes language runtime overhead and modular arithmetic scratch; recorded widths are proxies, not RSS. The explicit reference and validation harness allocate M and may not be used to measure streaming memory.

Use left-to-right binary exponentiation initialized at the base. For exponent e>=1 it performs exactly bitlen(e)-1 squarings and popcount(e)-1 additional modular multiplications. For a stream of factors q_i, the count is the sum of those costs. It is O(sum log q_i) and therefore O(log u + number of factors), but exact operation counts can favor either schedule. Chunk packing changes bit patterns, so the measured work is reported rather than presumed. It adds ordinary integer multiplications for chunk construction. Trial division enumerates primes with O(K sqrt(K)) candidate divisions (plus small prime-power generation overhead), repeated per base in this low-memory implementation. A segmented sieve would trade RAM for fewer enumeration operations. No speedup in end-to-end runtime is established.

Under DETFACT-02's conditional density bound ln K=O(sqrt(L ln L)), even the crude trial division work is exp(O(sqrt(L ln L)). This remains below exp(3 L^.75) asymptotically for a bounded number of bases or the upstream subexponential splitting budget, subject to the separate input Mstar and bit-cost premises. The upstream Theorem 1.3 explicitly claims a bounded-size integer M; our streaming evaluator does not replace the proof of that integer's construction or size. Compressing its execution supplies no proof of efficient relation discovery.

Do not substitute lcm(Mstar,S) for the product Mstar*S in the index argument: the group order is |H|*I, and the overlapping prime powers can matter. For p=17, |H|=4 and I=4, Mstar=4 and S=lcm(1,...,4)=12: lcm(4,12)=12 misses 16, while 4*12 covers it.

## 3. Replay design

Run node streaming_audit.mjs. The same function ran in the authoring JS runtime; Node was not separately invoked. The exact reference constructs S by iterative lcm, then uses left-to-right modular powering, cross-checked against a right-to-left implementation. The streamed path enumerates odd primes by trial division and tests individual prime powers, 64-bit chunks, and 256-bit chunks. It never constructs S or u.

Recreate DETFACT-06's saturation-interface fixtures on the same 12 known-factor moduli and B values with full or four-label banks. The known signed orders are exhaustive fixture oracles. Recreate the prior 2-by-2 lattice target exponents (2t or 14t according to pivot variant); verify each relation by modular powering. The fixture harness checks group-order coverage with the known factors, which are not used by the execution routines. This audits the saturation/split interface, not a rerun of the polynomial transport stage. Compare eight base residues and exact first successful split (base, chain index, divisor) for all three streamed modes on every fixture.

Edge tests include K=1, K immediately below/at/above powers of two, odd/even Mstar, zero and nonunit bases, repeated-factor N, and invalid parameters. Stress tests use a fixed 20-bit synthetic composite, a fixed positive Mstar, K=1024 through 65536, and three bases. Stress cases test execution equivalence; they are not factoring experiments. Counts of modular multiplications and trial divisions exclude the explicit reference lcm build and ordinary chunk packing work, and do not constitute wall-clock performance measurements. The receipt records maximum exponent operand widths, conservative chunk-product width bounds and split-chain work separately.

## 4. Formal certificate semantics

A compact execution certificate consists of (N,Mstar,K,a,s,x) and a deterministic enumeration rule. A verifier recomputes s and streams the odd prime powers in increasing prime order, then compares the residue x. The verifier must establish completeness and uniqueness of enumeration; accepting an arbitrary caller-supplied list is unsafe because it might omit a prime or use a wrong exponent. Explicit trial division and integer-power bounds suffice for the toy verifier. The certificate's small description is not a succinct proof of the potentially long computation. A proof-carrying implementation could separately certify enumeration and modular execution, but must account for proof generation and verification work.

Lean handoff: formalize the prime-factorization formula for lcm over a finite interval, the odd-part decomposition, modular power composition, and equivalence of the deterministic splitting trace. Use a verified prime enumeration theorem as a separate interface. No Lean compilation was performed in this environment.

## 5. Next gate

DETFACT-08: segmented prime-power enumeration and checkpointed streaming under explicit workspace limits, with reproducible native CPU wall-clock/RSS measurements if a local runner is available. Investigate cost-aware chunking, including precomputation reuse across multiple bases and the memory cost of retaining Mstar. No new factoring speed claim before testing a native implementation. Upstream PDF, actual relation producer, effective coverage and full Lean proof remain unresolved.

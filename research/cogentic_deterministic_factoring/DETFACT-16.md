# DETFACT-16: exact interval-LCM saturation certificates

Status at authoring: local finite replay passed; standalone Lean candidate submitted to CI. No claim of verification of Cogentic's relation-production theorem.

## Abstract roster certificate

Define PrimeLike(p) by 1<p and every divisor of p being 1 or p. Each roster entry (p,e) must satisfy PrimeLike(p), e>0, p^e<=K and K<p^(e+1). Labels must be unique and every prime p<=K must have an entry. For any such roster its product of p^e equals the recursively defined intervalLCM(K), starting with intervalLCM(0)=1 and using Nat.lcm on consecutive positive integers. The formal statement is independent of order and works also for an empty roster at K=0 or 1.

Proof: elementary prime divisor existence follows by strong induction (a proper nonunit divisor reduces the input). For p>1, strip powers of p by strong induction, obtaining n=p^e*r with r>0 and p not dividing r. If p is prime, gcd(p,r)=1. Another strong induction proves that a positive integer n divides M whenever all prime powers dividing n also divide M: strip a prime p dividing n, apply the hypothesis recursively to the smaller residual r, and combine p^e and r using coprimality and the lcm universal property. No fundamental-theorem-of-arithmetic axiom is introduced.

Each roster entry divides intervalLCM(K) because it lies in [1,K]. Distinct prime labels imply coprime powers, and induction plus lcm universal properties shows their product divides intervalLCM(K). Conversely each prime power p^a dividing i in [1,K] is bounded by K. If a>0, p<=K and the complete roster supplies p^e; maximality implies a<=e by monotonicity of powers, so p^a divides the roster product. The prime-power divisibility lemma gives i dividing the product. The interval lcm universal property and divisibility antisymmetry prove equality.

The kernel module uses core Lean only. Completeness, uniqueness, and maximality are explicit semantic hypotheses: it does not prove that a particular C sieve generates such a roster, nor does it prove a bound on its cost. The separate Python checker tests these conditions by trial division; it is intentionally expensive and stores a roster. That checker is not part of the fixed-arena production path. The segmented marking argument is that each odd composite <=K has an odd prime divisor <=sqrt(K); starting marking at p^2 preserves each prime and marks all composite multiples. Disjoint consecutive odd-index segments enumerate every eligible odd integer once. Include 2 separately and grow each power by multiplying while q<=floor(K/p). Native C refinement remains open.

## Composition

If a local subgroup order H divides Mstar and 1<=I<=K, then H*I divides Mstar*intervalLCM(K). This formal saturation implication is independent of how H and I were obtained. DETFACT-02's counting bound supplies the cap conditionally; its number-theoretic discovery premises remain separate.

The abstract lcm equality and DETFACT-15's verified equal-product execution theorem yield the streamed residue equivalence when all maximal powers are supplied. To produce the odd-only split exponent, separate the p=2 entry (or the empty case K=1) and the two-adic part of Mstar. The Lean file at authoring does not yet mechanize this filtered-list composition or certify enumeration completeness. The Python replay checks these steps against the explicit integer exponent, including the valuation, odd part and square-chain gcds.

## Replay

Run python saturation_certificate_audit.py. Local standard-library replay: 272 interval sizes, 1360 rosters, 165875 entries, 1360 streamed residues, 11320 split probes and seven adversarial rejection controls, all passed. The largest K is 65537. Independent reference uses math.lcm over the interval; the roster checker uses trial division for primality and exact set equality for coverage. Tests include segment boundaries, K=1, missing/duplicate/composite/out-of-range labels and malformed/nonmaximal/oversized powers. Supplied exponents and moduli are synthetic, not a benchmark for integer factoring.

The dedicated CI job compiles the standalone candidate with the repository toolchain and checks printed axiom markers. Keep the module standalone pending successful compilation. No aggregate import is included.

Next: finish kernel-gated odd-filter composition and connect to DETFACT-15; then return to Cogentic's actual relation-production proof. The upstream PDF and full formalization have not been obtained in this audit. Do not interpret the saturation and execution proofs as validation of the claimed deterministic subexponential factoring theorem.

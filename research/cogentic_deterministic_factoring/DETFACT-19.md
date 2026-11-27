# DETFACT-19: executable saturation roster and native first-strike arithmetic

Status at authoring: exact finite replay passed; standalone Lean composition candidate submitted to CI. The theorem statements concern a reference natural-number construction, not verified C semantics or efficient relation discovery.

## Base-list construction

Let R=floor(sqrt K), using Lean Nat.sqrt and its square bounds. Define denseMark(R,n) as a finite Boolean existential over divisors d<=R with 1<d, d^2<=n and d|n. For n in [2,R] a composite has such a divisor by DETFACT-18; a prime cannot. Filter the odd candidates <=R by the negated mark. This executable reference generator is sound and complete for odd prime labels p with p^2<=K. It discharges BaseSound and BaseComplete without assuming a supplied list or a primality oracle. It is a dense divisibility scan, not an efficient verified byte-array Eratosthenes implementation.

## First strike

For odd positive p and odd segment lower bound lo, set c=floor((lo+p-1)/p), r=max(p,c), and r'=r if r is odd, r+1 otherwise. Then F=p*r' is the least odd multiple of p at least lo and p^2. Ceiling division yields c<=q iff lo<=p*q. An odd quotient q with p*q>=lo and p*q>=p^2 satisfies q>=r; the smallest odd integer at least r is r'. Since p is odd, parity of p*r equals parity of r. Therefore F equals the native expression max(p*p,c*p) followed by adding p when that value is even.

An odd n>=lo is an eligible strike iff p^2<=n and p|n, equivalently n=F+2*p*t for some t>=0. In slot coordinates n=lo+2*h, this is exactly h=(F-lo)/2+p*t. The offset is integral since F and lo are odd and F>=lo. Intersecting with h<count gives the native segment loop's intended mark set. The proof is over natural integers, not C casts, finite-width arithmetic, memory or loop refinement.

## Executable maximal exponent

For p>1 and K>=1, repeatedly divide the bound by p while p<=current bound; count divisions. A structurally recursive fuel K suffices since floor(k/p)<k whenever k>0. Inductively the returned e satisfies p^e<=K<p^(e+1), using the two quotient inequalities. Each eligible p<=K gives e>0. The native multiplication loop uses the equivalent comparison q<=K/p; its final maximality implies the same e by uniqueness from DETFACT-17. Map the reference prime labels to this executable exponent; prove every entry valid, labels unique and coverage complete. Composition with DETFACT-16 proves roster product=intervalLCM(K) without base-list or roster hypotheses. DETFACT-17 then yields the streamed split-probe equality for this constructed list, given the supplied odd decomposition Mstar=2^s*u.

This is an executable abstract reference and an arithmetic specification for implementation refinement. It still filters the full global candidate list rather than implementing segmented byte arrays, and uses a slow dense base predicate. No uniform bit-cost theorem is claimed for this reference.

## Replay

Run node construct_audit.mjs. The finite audit compares the dense reference base list to independent trial primality, native first-strike to the quotient-parity formula, and slot progression to the direct square/divisibility predicate. All candidate offsets are checked for K<=4097; at larger indices check boundary and strike-adjacent offsets. The actual segmented label output is compared to trial primality, and the division-based exponent search is compared to the multiplication loop. The product is compared to exact iterative LCM. Number calculations are exact within these small ranges and the LCM and product use BigInt. The authoring JavaScript runtime executed this function; Node CI is a separate replay. Controls check square and inclusive boundaries, odd adjustment and maximal exponent transitions.

Receipt: {"schema":"DETFACT-19-exact","execution":"authoring JS runtime","indices":143,"base_candidates":930,"base_rosters":143,"first_strike_checks":247161,"offset_membership_checks":864914,"segment_configurations":569,"maximal_power_checks":78645,"lcm_checks":569,"negative_controls":6,"max_K":65537}

## Remaining gates

The original Cogentic PDF remains unavailable in this audit. The arithmetic pipeline from a constructed reference roster to split probes is within scope of the Lean candidate; efficient deterministic production of relation exponents and the source-specific analytic exceptional-set argument remain open. Next verify a segmented implementation refinement (including base sieve, concatenation, and native fixed-width operations), or prioritize source retrieval and actual relation production rather than additional resource scheduling. No full factoring complexity claim.

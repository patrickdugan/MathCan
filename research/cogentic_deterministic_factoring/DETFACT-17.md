# DETFACT-17: certified odd saturation stream and two-adic splitting

Status at authoring: exact finite replay passed in the authoring JavaScript runtime; standalone Lean composition candidate submitted to CI. The proof concerns supplied certificates and modular execution, not the upstream efficient relation producer.

## Composition theorem

Let Mstar>0 and K>=1, and let a roster contain one entry (p,e) for every prime p<=K with e>0 and p^e<=K<p^(e+1). Every entry is valid, labels are unique and coverage complete. DETFACT-16 establishes that its product is S=lcm(1,...,K).

Write Mstar=2^s*u with u odd. The existence of such a decomposition follows by stripping powers of 2. Its uniqueness follows because if 2^s*u=2^t*v and s<t, cancellation of 2^s shows u is divisible by 2, contradicting oddness. Symmetry excludes t<s, and cancellation gives u=v.

Define twoExponent by summing exponents attached to label 2, and oddFactors by keeping powers for all other labels in original order. By induction on the roster, its product equals 2^twoExponent times product(oddFactors). For a valid roster each retained prime other than 2 is odd, so that product is odd. For a complete unique roster and K>=1, twoExponent=t satisfies 2^t<=K<2^(t+1). For K=1 the empty roster has t=0. Uniqueness of maximal exponents follows from strict power monotonicity for bases >1.

The full saturation exponent is E=2*Mstar*S. Define c=1+s+t and Q=[u]++oddFactors. Then

    E = 2^c * product(Q)
    product(Q) is odd
    E / 2^c = product(Q).

By uniqueness, c is precisely the two-adic exponent of E. By DETFACT-15, the initial streamed residue is a^product(Q) mod N, including nonunit bases. The j-th gcd probe equals gcd(abs((a^((E/2^c)*2^j) mod N)-1),N) at every nonnegative j. Therefore, with a common scan order and bound, the first proper divisor is identical. The Lean theorem is pointwise; first-selection equivalence follows by the same finite search order. No guarantee that a divisor exists within a bounded scan is asserted.

## Replay

Run node odd_split_audit.mjs. The independent reference computes interval LCM iteratively using gcd, then strips powers of two from the explicit exponent. The fixture roster uses trial division and exact maximal-power enumeration. Three permutations include normal, reversed and even/odd order, demonstrating order-independent products and extraction. Five supplied Mstar values include a 65-bit odd value. Seven bases per modulus include zero, units, nonunits and N itself. Each square-chain index and the first proper gcd are compared. Negative controls cover missing/duplicate/composite labels, too-small/too-large power of two, zero Mstar and the necessity of oddness for uniqueness. The audit was run in the authoring JavaScript runtime, with its receipt committed. Node CI is a separate replay.

The standalone workflow compiles the unchanged DETFACT-15 and -16 modules and checks the composition and selected axiom markers under Lean 4.35.0; no aggregate import is added. The native C sieve and extraction routine remain outside this proof; validity, uniqueness and completeness of the roster are semantic hypotheses. No new timing claims.

Next: prove enumeration completeness with a simple abstract marking/prime-roster implementation, then examine implementation refinement. More importantly, retrieve the upstream Cogentic PDF and actual relation production argument; the original full complexity result remains unaudited.

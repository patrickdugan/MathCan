# DETFACT-15: streamed exponent equivalence and the singleton regime

Status at authoring: independent mathematical proofs; standalone Lean proof candidate and dedicated CI gate. The upstream deterministic factoring theorem is not verified.

## Semantics

For nonnegative integers a,n and a list of nonnegative factors Q, define E(Q)=product(Q), with empty product 1. Execute successive modular powers starting from a, reducing at each step and in the empty case. For the intended arithmetic n>=2; the Lean natural-number identities also use the total Nat.mod convention at zero. The fundamental equality follows from modular multiplication and power composition:

    ((a^e mod n)^f) mod n = a^(e*f) mod n.

Induction gives execute(n,a,Q)=a^E(Q) mod n. It applies to nonunits and to zero exponents using ordinary natural powers. Equal-product lists therefore give identical residues. Splitting Q into prefix and suffix gives checkpoint resumption exactly when the saved prefix residue is correct. A forged checkpoint is outside this premise; the theorem does not authenticate a state.

For every j>=0, the j-th square-chain residue is a^(E(Q)*2^j) mod n. The actual split probe is gcd(abs(x-1),n); for x=0 use 1, not truncated Nat subtraction. Thus all individual split probes agree, including nonunits and zero residues. A common scan order yields the same first proper divisor. The abstract theorem proves per-index probe equality, not a source-code simulation theorem for the C loop.

The odd saturation factor in DETFACT-07 is a particular list product. Connecting that list to lcm(1,...,K) requires the prime-factorization formula and complete prime enumeration. These are separate proof obligations. No claim that the list can be efficiently discovered from N alone follows.

## General singleton regime

For a maximal prime power q=p^a<=K, a>=1, we have p<=q and K<p*q. Therefore K<q*q. For any t with (2^t)^2<=K, q>2^t; any width w with q<2^w must satisfy w>t. Two such widths sum to more than 2t. Hence a conservative sum-of-widths packing guard at chunk width 2t must flush before combining two maximal powers. Oversize individual factors are executed separately. This proof applies to all prime powers, independent of primality beyond the premises. Taking t=8 yields the DETFACT-14 sufficient threshold K>=65536 for 16-bit chunks. It is not asserted to be the sharp threshold. The guard itself does not establish minimum arithmetic cost or actual wall-time optimality.

## Replay

Run python stream_semantics_audit.py. Independently test modular power composition on synthetic moduli, zero/nonunit bases, empty and zero-factor lists, every checkpoint boundary, equal-product merges and nine square-chain indices. Check maximal powers, width guards and streamed packing with multiple segment widths across thresholds 2^(2t), t=1..9. Negative controls cover packing at small K, omission of a prime power, and an incorrect checkpoint. The finite checks are separate from the Lean theorems.

The standalone workflow runs the pinned Lean toolchain, prints selected axiom dependencies, rejects specified admitted-proof/native-reduction markers, and runs the Python replay. The module is deliberately not yet imported by MathCan.lean; integrate only after the standalone kernel gate succeeds. The original Cogentic paper raw URL still returns an unsupported binary content type, the GitHub contents request with base64 returns an empty payload, and the blob-text request fails UTF-8 decoding. The full upstream PDF and formalization remain unavailable for this audit. Recent independent summaries continue to describe the companion Lean proof as announced but not released. See the pinned source folder and https://qed.bot/a/google-2026-11-25 for release status. No new upstream proof claim.

Next: validate the exact lcm-to-prime-power list semantics and bounded enumeration as separate mathematical obligations, then prioritize retrieving and auditing the actual number-field relation producer and its effective analytic coverage. Resource scheduling experiments remain at the static16 baseline unless a fresh, meaningful performance hypothesis warrants them.

# NOR-24 sequential witness and conditional support counts

Mathematical companion to the prospectively registered learned coordinate-auditing experiment in Compactification-Theory at research/nor24_adaptive_audits/REGISTRATION.md. Builds on merged NOR-23, where a fixed independent blind alteration of r hidden output coordinates is detected by a uniform audit of k distinct positions with probability 1-C(m-r,k)/C(m,k).

The Lean 4.35 standard-library module MathCan/NOR24SequentialWitness.lean introduces ordered authentic exact-value witness transcripts and proves:

1. If two target worlds agree on every coordinate already queried, their entire ordered authentic witness transcripts are equal.
2. Any deterministic adaptive policy that sees only public context and that transcript chooses the same next coordinate in the two indistinguishable worlds. Hence a clean witness history alone cannot reveal differences outside inspected positions.
3. A declared attack support that is disjoint from every checked coordinate permits the changed target to pass every audit check, provided the attack changes nothing outside support.
4. For a finite support of s positions, after t inspected clean support positions, the exact number of fixed-radius r attack subsets still compatible with a no-hit transcript is C(s-t,r). The proof uses the standalone k-subset enumerator previously kernel-verified in NOR-23.
5. The Pascal hit/miss partition C(n+1,r+1)=C(n,r)+C(n,r+1) establishes the finite arithmetic underlying one-step posterior updates.

The applied controller assumes templates defined entirely from the public prediction: the last 96 output coordinates, the 96 highest-magnitude predicted coefficients, a 96-coordinate window at the public delay+spacing, and the entire output as a uniform background. It fits only the mixture over these templates from labeled TRAIN attacks, then compares a sequential Bayesian no-hit update with static ranking, uniform auditing, shuffled ranking and a privileged support-aware oracle on disjoint TEST public sources.

The sample weights, independence of true attacks from challenge generation, authenticity of the external witness, training provenance and wall-clock speed are explicitly empirical assumptions. Kernel proofs do not establish cryptographic unpredictability, calibration of the prior, or general RRC25 soundness outside the declared program family. A negative prospective outcome is to be retained as a negative result.

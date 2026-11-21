# RH-CRYPTO-26 / RH-01: assumptions and cryptographic consequences

**Dated:** 2026-11-22. **Status:** research ledger; source-reviewed implications with explicit theorem and attack gates. **Canonical mathematics home:** MathCan. This note complements the source-pinned proof-route work in [rh_proof_distillation](../rh_proof_distillation/PROVENANCE.md).

## 1. Formal verification and scope

- The Lean/Mathlib communities report that the 175,187-module Alpöge–Claude library checks, that its RH statement agrees with Mathlib's canonical \`RiemannHypothesis\`, and that independent kernel implementations accepted the export. Their 2026-11-21 statement explicitly certifies the formal statement and proof: https://leanprover-community.github.io/blog/posts/riemann-hypothesis/
- Andrew Sutherland reports independent compilation, axiom checks (\`propext\`, \`Classical.choice\`, \`Quot.sound\`), proof replays, and statement comparison: https://math.mit.edu/~drew/grh/ . Cite the time-stamped log for the status of each individual check. Our own MathCan source audits do *not* independently reproduce this whole-proof verification.
- The formal **GRH** endpoint here applies to **Dirichlet L-functions**. It does not by itself prove analogous assertions for all Dedekind, Hecke, Artin, or automorphic L-functions. The announcement describes wider extensions as prospective.
- The result is mathematical; official prize status and a human-readable exposition have separate processes. An independent kernel check answers a different question from extracting the proof's operative mechanism.

## 2. Assumption matrix

| Assertion | Dependency | Evidence class | Status for RH-CRYPTO-26 |
| --- | --- | --- | --- |
| RH for the Riemann zeta function | Alpöge–Claude theorem in Mathlib definition | Independently reported formal-kernel certification | Accepted as an externally checked theorem; original proof not rebuilt in MathCan |
| GRH for Dirichlet L-functions | Formal \`Main.lean\` Dirichlet endpoints | Independently reported formal-kernel certification | Within published scope |
| RH for finite-field curves (Hasse–Weil) | Classical unconditional theorems | Established theorem, unrelated to new RH proof | Already available |
| GRH for general number-field/automorphic L-functions | Stronger unproved hypotheses | Research hypothesis | Requires a new theorem and type-level check |
| Effective primes in arithmetic progressions | Appropriate Dirichlet-GRH analytic estimates | Theorem consequence, conditional on correct effective constants | Relevant to prime/field selection |
| Small quadratic nonresidues | Character-sum bounds under Dirichlet GRH | Theorem consequence | Relevant to deterministic finite-field routines |
| Dense Semaev relation witnesses on prime-coordinate bases | Curve-specific and prime-restricted character sums | Open empirical/math hypothesis | Requires independently checked count and search-cost proof |
| Faster ECDLP for secp256k1 | Full curve-specific algorithm and cost proof | Unestablished attack hypothesis | No result follows directly from RH/GRH |
| Efficient generic polynomial-system solving | Constructive complexity theorem | Unestablished algorithmic hypothesis | Point-count bounds alone insufficient |
| STARK/KZG/IPA/Poseidon security failure | Concrete adversarial construction under stated parameters | Unestablished attack hypothesis | Analyze each scheme and assumption separately |
| Classification in an Impagliazzo universe | Complexity-theoretic cryptographic existence results | Open complexity statement | RH is compatible with multiple worlds |

## 3. Quantifier and size traps

1. **Prime in a residue class.** GRH strengthens effective bounds for the least prime satisfying \`p ≡ a (mod m)\`. A bound polynomial in \`m\` can still be exponential in the bit length of \`m\`. Benchmark output-sensitive parameter construction; record integer arithmetic and primality certification costs.
2. **Roots of unity.** A multiplicative subgroup of size \`2^k\` exists in \`F_p^×\` exactly when \`2^k | (p-1)\`. Constructing an NTT-friendly field also requires practical modular reduction and proof-system-specific parameters. Congruences of the field **modulus** are different from congruences of x-coordinate representatives within a fixed field.
3. **Quadratic character on a curve.** An x-coordinate lifts to \`E(F_p)\` when \`x^3 + ax + b\` is a square in \`F_p\`. Ordinary Dirichlet-GRH bounds about rational primes in fixed congruence classes do not imply improved Semaev-decomposition density. Prime-valued x restrictions introduce new sums of polynomial characters over primes.
4. **Counting versus finding.** Even a power-saving estimate for the number of points on a family of varieties need not give a witness-finding algorithm. Record dimension, degrees, constants, input bit complexity, memory, and witness verification.
5. **Variable assumptions.** In any reduction using an L-function, record conductor, modulus, field degree, and the range of uniformity. A theorem valid for each fixed input may have constants too large for scalable cryptography.

## 4. Mechanism to inspect in the source-pinned RH chain

MathCan's existing route audits locate the relevant suppliers: \`GeoOne\`, \`PlanEx\`, \`TLiftK\`, the Galois-row interface, automorphic windows and the final character estimate. See [MAIN_PROOF_SOURCE](../rh_proof_distillation/MAIN_PROOF_SOURCE.md) and [GEOMETRY_THETA_DEEP_GATES](../rh_proof_distillation/GEOMETRY_THETA_DEEP_GATES.md). These are proof-route and hypothesis audits, and must retain their original evidence labels.

Extraction questions:

- Does the proof supply an **effective computable constant** or an existence theorem with uncontrolled dependence on the family?
- Can a prime-distribution inequality be implemented as a witness-search routine, with explicit runtime and memory bounds?
- Are any reductions specific to Dirichlet characters, or do they require unproved transfer to polynomial character sums over a finite-field curve?
- Are theta-lift dimensions and geometric witness antecedents populated in the source proof at the intended invocation?

A positive result must quote an exact source declaration or prove a separate lemma with a full quantified statement. Heuristic numerical fits are experiment results.

## 5. Proposed experiments and acceptance gates

**RH-02 (zk-rusto-no-bitcoino):** NTT prime discovery. Freeze bit-width bands, \`2^k\` constraints, a reference search algorithm, and primality certificates. Compare runtime and arithmetic cost. Reporting a lower conditional bound is not a measured improvement.

**RH-03 (semaev-index-calculus):** Paired, toy-prime-order curves. Exactly match the number of x-coordinates and signed points between random, prime-integer-coordinate, arithmetic-progression-coordinate, and small-smooth-integer-coordinate bases. Freeze seeds, curves, target schedules, pair precomputation, S3 and point verifiers, exact rank and key-recovery criteria, and a generic \`sqrt(N)\` scale reference. Count every group operation used in relation acquisition and recovery, as well as peak tracked memory. The integer-coordinate conditions depend on the chosen representatives \`0,…,p-1\`; a field automorphism or coordinate change need not preserve them. Leave an independent confirmation split sealed during development.

**RH-04 (zk-rusto-no-bitcoino):** Reduced-round algebraic-hash systems only. Report exact parameters, chosen-plaintext/preimage model, solver version, full system-solving costs and independently checked witnesses. Findings about reduced rounds do not transfer automatically to deployed full rounds.

**RH-05 (EvalMath):** Count-to-find gym. Input a theorem giving a solution-count estimate, a family of polynomials and a resource budget. Score proposed **algorithms** by verified witness, runtime, memory and proof of uniformity. Include nulls where plenty of points exist but a naive search is costly.

**Escalation threshold:** A claim about Bitcoin ECDSA needs a full attack on a cryptographically meaningful prime-order curve with asymptotic or independently benchmarked total cost below the best applicable generic methods. Even this would not resolve the five Impagliazzo worlds.

## 6. Reproducibility and provenance

Keep experiments in their native repositories. Link immutable commit SHAs and machine-readable receipts back here. Report development and confirmation results separately; avoid tuning on unopened controls. Use an explicit status taxonomy: formal theorem, theorem under extra hypotheses, finite exact computation, numerical observation, and conjecture.

References:

- Lean/Mathlib joint statement: https://leanprover-community.github.io/blog/posts/riemann-hypothesis/
- Sutherland verification: https://math.mit.edu/~drew/grh/
- Original announcement: https://alpo.ge/remark.pdf
- Source pinned in existing MathCan audits: https://github.com/leanprover-community/riemann-hypothesis/tree/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3
- Existing Semaev exact benchmarks: https://github.com/patrickdugan/semaev-index-calculus

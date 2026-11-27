# DETFACT-06: conditional end-to-end certificate pipeline

Status: independent synthetic composition audit. The pipeline verifies a supplied relation bank and attempts to split a modulus. It does not implement Cogentic's efficient relation producer, prove effective coverage, or establish the upstream asymptotic theorem.

This combines the conditional results in DETFACT-AUDIT-01 and DETFACT-02 through DETFACT-05. Primary source: [pinned Cogentic theorem statements](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/README.md). Original PDF and companion Lean proof have not been retrieved. No Lean kernel build is claimed.

## 1. Certificate and status contract

The toy checker receives odd N>=9, B>=5, an explicit minimum relation count and resource limits, and a bank of records. Each record contains a distinct prime label 4<ell<=B, a degree-four preconditioned polynomial pair with common m, a 2-by-2 integer relation matrix for the units (ell,2), and two pairs of explicit polynomial identities with declared global signs. Fixed toy parameters: z=3, Q=6*ell, c=4Q+3. The general preceding lemmas allow wider dimensions and degrees; this implementation deliberately restricts them.

For each record:

1. Reject duplicate or inadmissible labels, check the relevant unit gcds, and validate the degree-four polynomial pair, its root, binary irreducibility, small-prime conditions, coefficient bounds and target root patterns.
2. Check both exact integer polynomial identities for each column and their required denominator units. Evaluate the localized fractions and verify their equality across fields and the signed modular column relation. A proper gcd may already return a divisor.
3. Compute the target-specific multiplier for the nonsingular integer pivot, check the integer isolation witness, and verify the resulting positive even exponent by modular powering.
4. Require at least the configured number of distinct covered prime labels. Compute the uniform index cap K_exact from DETFACT-02; enforce a cap budget before constructing lcm(1,...,K). Combine verified exponents via lcm and multiply by the saturation factor and 2. The conditional subgroup-index proof supplies the common p-1 exponent for all prime factors; the checker has no access to them.
5. Try a bounded deterministic base scan of the two-adic splitting chain. A returned divisor is checked exactly. If the scan runs out, return unresolved. A guaranteed subexponential construction of adequate splitting witnesses is still an upstream obligation.

Statuses: factor (with verified proper divisor), invalid (violated certificate/domain), unresolved (valid-looking but insufficient witness, singular pivot, zero evaluated denominator, or exhausted budget). This toy checker takes structured BigInt records generated inside the script. It is not a hardened external JSON parser and does not bound all allocations or reject arbitrary ill-typed objects. Some invalid records abort the bank rather than searching around them; unit checks short-circuit. All resource limits are toy engineering choices, not upstream parameter choices.

## 2. Conditional soundness

For each successfully verified relation column, two-field transport gives a signed product of the two units. The column-lattice isolation lemma proves a positive target exponent annihilates the corresponding prime label modulo N. Distinct certified prime labels give the monomial count from DETFACT-02. Its uniform index cap implies every prime-factor group order p-1 divides the saturated exponent, even with repeated prime factors in N. The splitting scan's final gcd is either a proper divisor or gives no successful result. Thus every returned factor is sound, and the exponent guarantee is conditional on the verified bank and the previously proved counting lemma. A finite scan is not a proof of guaranteed splitting.

The minimum count of four used in the fixtures is a test threshold, not a quantitative asymptotic density condition. For arbitrary N a bank that meets this threshold can still yield an excessively large index cap. The analytic coverage theorem needed to guarantee both a sufficient bank and the desired cost remains open in this audit.

## 3. Replay and controls

Run node pipeline_audit.mjs. The exact BigInt fixtures are built over 12 synthetic odd composite moduli with known factor multisets; they include squarefree two- and three-prime cases and nonsquarefree cases. For B in {19,23,31}, run the full eligible label list and a restricted four-label list. The fixture producer exhaustively enumerates signed orders to synthesize relation columns, and constructs simple rational polynomial identities for their modular signs. The checker never calls the oracle or receives the factor multisets. The test harness checks the final exponent against the known p-1 values only after the pipeline returns. This is an oracle-backed composition test, not a benchmark against integer factoring algorithms or a reconstruction of actual number-field relation discovery.

Controls include a short list, duplicate or composite labels, an out-of-bound target, invalid polynomial root, forged quotient, wrong sign, incompatible images, valid singular pivot, budget exits, nonunit and zero evaluated denominators, and a target gcd that immediately gives a divisor. A factor-returning control verifies the proper divisor independently. The same audit function ran in the authoring JavaScript runtime and generated pipeline_receipt.json; Node itself was not separately invoked.

## 4. Research boundary and next step

A credible upstream proof audit now needs the source PDF or Lean companion, and a separate relation-production receipt with no hidden factor/order oracle. In particular it must establish the actual ideal/unit relation construction, rank or target-isolation existence, the effective exceptional-set counting argument, and bit-size bounds for all intermediate arithmetic and the full search. The small checker proves no speed claim. Its positive cases are intentionally generated, not held-out evidence of coverage.

For DataGoblin/Lean research use the status contracts as verifier exercises, with independent synthetic train and test parameter families. The small pipeline gives a target for exact certificate diagnosis and composition, not a learned factoring benchmark. A future formal module should first prove the concrete localization-to-relation transport, integer lattice isolation and index saturation interfaces; no kernel compilation has been performed here.

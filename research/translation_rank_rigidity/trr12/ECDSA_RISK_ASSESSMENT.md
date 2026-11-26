# ECDSA risk and an evidence-driven evaluation program

Date checked: 2026-11-26. This document continues Strategy V's examination
of the relationship between representation bounds and computational cost.
It also specifies separate signer, quantum and migration evaluations for
the broader security paper. All executed curve experiments use synthetic
small fields. The secp256k1 exercise counts a symbolic circuit from public
constants.

## Current assessment

TRR-11 supplies a universal theorem within its stated interpolation model:
the least common ordinary total-degree bound across the two coordinate
pairs is ceil(N/3), for
every assigned identity value on a smooth generalized Weierstrass curve
with finite odd marked order N>=19, assuming 2, 3 and N are nonzero in the
field. Its theorem and complete hypotheses are in the
[TRR-11 overview](../trr11/README.md).

The relevant next question is how an attempted scalar-recovery algorithm
would have to use a representation covered by that theorem. TRR-12 makes
the need for that connection concrete. It gives an exact division-free
circuit for the forward decoder with O(log q) field gates. The same target
therefore has the proved large polynomial degree and a short evaluation
program. The [written proof and exact controls](SCOPE_PROOF.md) explain
both statements.

The existing results give a rigorous rejection criterion for certain
representations. A practical ECDSA compromise claim requires a successful
forgery or key-recovery mechanism and its resource analysis. The research
currently contains the restricted-model theorem, reproducible toy checks,
and a verified control for the difference between degree and circuit cost.
No scalar-recovery candidate is introduced in this update.

## 1. Define the security event

Let G have prime order n, let d be a signing key and Q=[d]G its public key.
ECDSA uses a nonce k, R=[k]G, r derived from x(R), and

\[
s=k^{-1}(z+rd)\pmod n.
\]

Here z is the message representative. The exact field-to-integer conversion
and reduction used to obtain r are part of the signature specification.
The x-coordinate interpolation theorem is formulated over the coordinate
field; an ECDSA reduction must also account for that conversion. [S1]

A public-key inversion experiment asks for d from G and Q, and verifies
the answer independently by checking [d]G=Q. A forgery experiment can have
a different goal: produce a valid signature on a fresh permitted message
under the declared query model. Same-message signature transformations and
predictions of a few coordinate bits need their own success definitions.

The following threat models answer different operational questions.

| Model | Adversary access | Evidence that changes this assessment |
|---|---|---|
| Classical ECDLP | Public curve, G, Q; fresh uniform scalar | Reproduced scalar recovery with complete cost and credible scaling |
| Signature-specific attack | Messages and signatures, with declared signing queries | A fresh-message forgery or recovery, including the access needed |
| Nonce or implementation leakage | A stated nonce defect, timing signal, fault, or device access | Reproduction on the affected signer and a bounded leakage model |
| Quantum ECDLP | A specified fault-tolerant architecture and public Q | Verified circuit resources, error budget, success rate and hardware assumptions |
| Authorization or migration failure | A concrete spending policy and implementation | A transaction or protocol trace violating the intended policy |

Each row gets its own evidence status. A probability of compromise also
requires a time horizon, an adversary budget, the deployed signer, and the
exposure of the relevant public keys. The interpolation experiments do not
identify those inputs.

## 2. What the new circuit control establishes

The target in TRR-11 is the forward map (P,Q) -> f_u(P+Q). A direct
construction uses polynomial zero indicators over a finite field to
select the secant formula, doubling formula or assigned identity value.
Binary powering evaluates those indicators efficiently. Every operation
is recorded in a gate list and charged.

| Quantity | Executed or derived result |
|---|---:|
| Complete input pairs on six toy curves | 4,624 |
| Circuit evaluations over every assigned u | 130,464 |
| Inverse pairs checked | 160 |
| Tangent pairs checked | 160 |
| Failures after corrupting the identity selector | 320 |
| Multiplications at the public secp256k1 field size | 1,523 |
| Additions/subtractions at that size | 12 |
| Multiplicative depth of that circuit | 507 |

The last three rows count a symbolic program from the published parameters;
they contain no cryptographic-size point evaluation. The independently
reviewed receipt retains every small-field gate trace. The general
finite-field construction has a written proof, with a future Lean
formalization explicitly outstanding.

For a division-free circuit with degree-one coordinate inputs, binary
multiplication gates and multiplicative depth h, ordinary degree is at
most 2^h. Thus the direct degree-to-depth implication is

\[
h\ge \lceil\log_2\lceil N/3\rceil\rceil.
\]

Using the published secp256k1 n gives 255. This is a derived
resource statement, and the exhibited depth-507 program is compatible
with it. Multiplicative depth, gate count, expanded degree, representation
size and bit-operation cost must be recorded separately.

SEC 2 specifies secp256k1 over a 256-bit prime field, with equation
y^2=x^3+7, a prime subgroup order n close to 2^256 and cofactor one. Its
field characteristic and subgroup order are different. These are the
large-order, tame parameters relevant to TRR-11. Completing the formal
small-order and characteristic-dividing-order cases strengthens the
mathematical classification, while the security-transfer question for
these parameters is already present in the covered regime. [S2]

## 3. The classical baseline and the algebraic research target

Generic collision search for a prime-order group has work proportional to
sqrt(n), giving the familiar approximate 128-bit work scale for a 256-bit
order. Shoup's lower bound applies to generic algorithms, which receive
encodings abstracted from exploitable coordinate structure. Its model
boundary matters for any algebraic method using explicit coordinates.
[S3]

Efficient automorphisms and optimized field arithmetic affect practical
rho costs. Comparisons should use a competent implementation with the
applicable automorphisms and should separately measure walk iterations
and cost per iteration. The analysis of Bos, Costello and Miele shows the
importance of representative selection and fruitless cycles when using
automorphism speedups. [S4]

Semaev's original formulation gives a conditional route: a sufficiently
efficient solver for specified bounded modular polynomial systems leads
to faster discrete logarithms. This identifies a precise place to test
an algorithm. An intermediate relation, a small written equation or an
observed degree drop leaves the cost of collecting enough useful
relations and completing the recovery to be measured. [S5]

For a proposed polynomial-system method, record the variable count,
equations, maximum degrees reached, matrix dimensions, density and rank,
coefficient arithmetic, memory traffic and usable relations per unit work.
Kosters and Yeo explain how small first-fall degree can coexist with
problematic solving heuristics in binary-field summation-polynomial work.
That result motivates checking the heuristic in the exact field family
being studied. [S6]

An integer-factoring advance would enter the paper as a result about its
own problem. Its effect on ECDLP requires a specified reduction or shared
mechanism, including the cost of transferring that mechanism to the
prime-field curve family. The current assessment makes no assumption
about an undisclosed implementation.

## 4. The next mathematical obligation for Strategy V

Specify a class of recovery algorithms A and a charged resource C(A,N).
Then state a conversion theorem that takes a successful A and constructs
the representation constrained by TRR-11 or the earlier feature-rank
theorems. The theorem must give explicit bounds on that representation
in terms of C and must specify its domain and success probability.

Useful questions for such a claim include:

- Can every feature be evaluated from public point coordinates? A feature
  defined using the unknown scalar merely moves the recovery task into
  the input map.
- What cost is paid to construct coefficients, charts, auxiliary
  variables and exceptional-case data? A per-target online count requires
  a separate precomputation ledger.
- Does the conversion preserve arithmetic-circuit sharing? Expanding a
  repeatedly squared expression can multiply its degree without
  multiplying its evaluation time at the same rate.
- Does the argument use identities on every group point or average-case
  success on a sampled distribution? An exact universal interpolation
  bound needs an additional theorem to constrain the latter.
- How are rational denominators, branching, extension-field dimension and
  memory charged? Each permitted feature changes the model being bounded.

The circuit in this package is a required control for every proposed
conversion. It evaluates the constrained forward map at small cost, so a
conversion that assigns it exponential evaluation cost has failed its
resource accounting.

The earlier common-pole-budget and feature-rank results offer a focused
continuation of Strategy V: identify a restricted feature family, prove
that a proposed recovery method must use it, and charge feature
construction. A distinct recovery mechanism would merit its own strategy
identifier. The risk assessment and its evaluation contract continue the
current strategy without presupposing such a mechanism.

## 5. Preregistered empirical evaluation

The accompanying evaluation_plan.json records which work has run and
which depends on a candidate. Only the circuit-scope control is executed
by this update. Its CI job has a ten-minute timeout and standard-library
dependencies.

### Blind toy recovery

The generator creates synthetic prime-field curves, a marked prime-order
subgroup, fresh uniform scalars and their public points. The candidate
receives public inputs through a fixed interface. The independent verifier
holds labels and checks recovered scalars using a separate group-law
implementation. The candidate's process receives no reference table or
hidden scalar through serialized metadata, filenames or seeds.

Development and evaluation seeds must be committed before the evaluation
run. Tuning uses its own curves. Splits by curve and by larger parameter
sizes assess different forms of generalization and are reported
separately. A target split on one fixed curve alone permits curve-specific
precomputation, whose cost must be included.

Use a prime-field j=0 family together with a general family. Record order,
cofactor, relevant automorphisms and exceptional mathematical structure.
Interval-constrained scalars, anomalous curves and other specially weak
instances receive separate labels. Extension-field cohorts can test
additional hypotheses, with a transfer argument required before their
results inform a prime-field claim.

The initial proposed smoke cohort uses 16- and 20-bit subgroup orders.
For each size, use two independently generated curves, eight fresh targets
per curve and two algorithm seeds. A candidate must pass this functional
stage before a larger pilot at 24 and 28 bits is enabled. These bit sizes
are a plan; no recovery measurements at those sizes are claimed here.
Budget each candidate job at ten minutes and two GiB, retaining its
timeouts. A larger campaign needs a measured pilot before its budget is
set.

### Cost ledger

Measure first-target and amortized costs explicitly:

\[
W_{first}=W_{pre}+W_{target},\qquad
\overline W(M)=W_{pre}/M+W_{target}.
\]

Precomputation includes model training, feature construction, relation
collection and reusable tables. Per-target work includes target-specific
relations, linear algebra or descent, and final verification. Record
field operations, group operations, CPU/GPU time, maximum resident memory,
storage and communication alongside the useful success count. State the
number M of targets over which the precomputation is amortized.

A success after an aborted attempt inherits the failed attempt's cost.
Publish the whole run population. Report success at fixed budgets and
time-to-success distributions with censored timeouts; a regression through
only successful small instances hides the hard part of the experiment.

### Scaling and promotion gates

Fit log2(work) against b=log2(n), including an intercept, and retain larger
sizes for prediction checks. Use a curve-level bootstrap or another method
that respects shared precomputation within a curve. Compare field-operation
and runtime fits, and retain the raw records so a reviewer can change the
model. A fit below exponent one-half on a short range motivates a larger
test. A claim about asymptotic behavior also needs an argument explaining
why the mechanism persists as the family grows.

Promote a result through the following evidence gates:

| Gate | Required artifact | Interpretation |
|---|---|---|
| Functional | Independently verified recovery on fresh toy instances | The candidate implements the stated task |
| Comparative | Full-cost comparison with a suitable rho baseline | A measured advantage on the tested distribution |
| Predictive | Correct predictions on unseen larger sizes and curves | Evidence that the measured trend persists over the tested extension |
| Structural | A derivation of the claimed complexity with checked assumptions | A supported family-level hypothesis or theorem |
| Deployment assessment | Reviewed concrete resource estimate and access model | A basis for assessing a particular system's exposure |

The phrase strong candidate for a practical attack should be reserved for
a mechanism that has cleared meaningful comparative and predictive gates,
with a plausible resource projection and remaining assumptions stated.
The current interpolation theorem has its own stronger mathematical
status within its model; it supplies no corresponding recovery benchmark.

## 6. Evaluate the signer independently

Nonce reuse, biased generation or leakage can compromise an affected
signer without an improvement to public-point inversion. RFC 6979 gives a
deterministic nonce construction. Its deployment still depends on correct
key generation and implementation. The Minerva work demonstrates recovery
from nonce-length timing leakage in affected ECDSA implementations and
explains why deterministic nonces leave that leakage relevant. Its
smartcard case uses secp256r1. [S7, S8]

For a controlled signer evaluation, pin the library, compiler, flags,
architecture and nonce function. Exercise known-answer and cross-library
tests, permitted entropy failures, restart behavior, domain separation and
fault handling. Test whether secret-dependent timing or memory behavior
survives on the intended hardware. A passing timing screen has a stated
sample size and leakage sensitivity; it is one item in an implementation
assurance argument.

libsecp256k1 documents constant-time and constant-memory-access signing,
RFC 6979 support and optional runtime blinding. The exact build and its
application interface remain part of an evaluation. [S9]

For the repository program, implementation findings are classified by the
affected signer and access condition. A mathematical-model result and a
device-specific leakage result belong in separate evidence records.

## 7. Quantum capability and public-key exposure

A 2026 PRX Quantum paper reports secp256k1 circuits with at most 1,200
logical qubits and 90 million Toffoli gates, or 1,450 and 70 million.
Its physical estimates depend on fault-tolerant hardware assumptions,
including physical error rates, connectivity and control latency. The
published evidence concerns circuit resources and their verification;
cryptographic-size hardware execution is a separate milestone. [S10]

Maintain a resource ledger containing circuit revision, logical qubits,
gate count and sequential depth, code distance, physical error model,
magic-state supply, control reaction time, total success probability and
restarts. Charge preprocessing and the lifetime of a prepared quantum
state separately from online work. Sensitivity analyses must keep their
hardware assumptions visible and should not convert an architecture model
into a calendar prediction.

Bitcoin's deployed BIP340 Schnorr signatures retain the secp256k1 discrete
logarithm assumption. A scalar-recovery capability would affect those
signatures as well as ECDSA. [S11]

BIP341 puts a public output key directly in a Taproot output. BIP141's
P2WPKH form commits to a public-key hash and reveals the key in the spend.
Applying those rules shows why reuse or an off-chain key disclosure can
extend exposure while other outputs remain spendable. [S12, S13]

For each controlled wallet fixture, record the public points available,
the earliest disclosure, every spending path and the value still
controlled by that authorization. An on-spend scenario depends on whether
recovery and propagation finish within the remaining confirmation window.
That window is a distribution, and the evaluation should specify relay,
fee and confirmation assumptions instead of assuming a fixed deadline.

This also matters for keyless constructions. BIP341 describes internal
NUMS points with unknown discrete logarithms, and its key path accepts
signatures under the public output key. It follows that a solver for that
output key's logarithm could use the key path even when no participant
originally knew an internal scalar. This is an inference about standard
Taproot; a custom Keyless-CHECKSIG construction requires its own audit.
[S12]

## 8. Migration work that can be evaluated now

NIST's final FIPS 204 and 205 specify ML-DSA and SLH-DSA signatures.
IR 8547 became final on October 27, 2026; it schedules deprecation of
quantum-vulnerable public-key cryptography after 2030 and disallowance
under NIST standards after 2035, with earlier requirements for some
federal systems. These dates govern standards transitions. [S14-S16]

The canonical Bitcoin texts checked on this report's date label BIP360
and BIP361 Draft. BIP360 proposes a script-tree output without Taproot's
key path and addresses long exposure. BIP361 depends on a future
post-quantum signature proposal. Their text describes proposed changes
whose activation would require Bitcoin's own process. [S17, S18]

For Bitcoin protocol work, the useful prototype is an authorization and
transaction experiment on controlled fixtures. Measure serialized bytes,
verification cost, peak memory, malformed-input behavior and agreement
between implementations. Include key rotation, backups, recovery paths,
threshold requirements and hardware-wallet limits in the fixture contract.

A hybrid policy must specify its Boolean condition. Requiring both
classical and post-quantum signatures has a different failure condition
from accepting either. Test every fallback and recovery branch against
the intended policy. An output advertised as script-only should receive
a control that checks whether the consensus format still permits a key
path.

Migration planning depends on lead time and the duration of exposure.
That work can proceed while the underlying hardware timeline remains
uncertain. Keep an explicit distinction between a usable signature
primitive, its implementation, and a consensus-compatible transaction
format.

## 9. Work priorities and remaining obligations

The next Strategy V task is to state one candidate's public feature map
and the cost-preserving reduction required to apply a representation
bound. The circuit control in this package becomes an obligatory test of
that reduction. CI can continue to reproduce the completed mathematical
results at low cost.

Actual scalar-recovery scaling runs wait for a specified candidate and
the blind interface. Signer tests and quantum-exposure fixtures can
progress as separate tracks with their own success conditions. The
matching-characteristic lower bound and small-order Lean interfaces
remain mathematical proof work, as recorded in TRR-11.

For every future claim, retain the source revision, admissible inputs,
adversary access, complete cost, tested distribution, failed cases,
independent replay and the precise operational implication. A claim with
an unresolved proof obligation remains labelled at that boundary.

## Sources checked

- [S1: SEC 1, ECDSA specification](https://www.secg.org/sec1-v2.pdf), section 4.1.
- [S2: SEC 2, secp256k1 parameters](https://www.secg.org/sec2-v2.pdf), section 2.4.1.
- [S3: Shoup, generic discrete-log lower bounds](https://www.shoup.net/papers/dlbounds1.pdf).
- [S4: Bos, Costello and Miele, practical curve security](https://www.microsoft.com/en-us/research/wp-content/uploads/2014/01/644.pdf).
- [S5: Semaev's summation-polynomial construction](https://eprint.iacr.org/2004/031).
- [S6: Kosters and Yeo on summation-polynomial heuristics](https://arxiv.org/abs/1503.08001).
- [S7: RFC 6979](https://www.rfc-editor.org/rfc/rfc6979).
- [S8: Minerva authors' research site](https://minerva.crocs.fi.muni.cz/).
- [S9: libsecp256k1 documentation](https://github.com/bitcoin-core/secp256k1).
- [S10: Babbush et al., PRX Quantum 7, 031001 (2026)](https://journals.aps.org/prxquantum/abstract/10.1103/j3xf-bw18).
- [S11: BIP340](https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340.mediawiki).
- [S12: BIP341](https://raw.githubusercontent.com/bitcoin/bips/master/bip-0341.mediawiki).
- [S13: BIP141](https://raw.githubusercontent.com/bitcoin/bips/master/bip-0141.mediawiki).
- [S14: FIPS 204](https://csrc.nist.gov/pubs/fips/204/final).
- [S15: FIPS 205](https://csrc.nist.gov/pubs/fips/205/final).
- [S16: NIST IR 8547 final](https://csrc.nist.gov/pubs/ir/8547/final).
- [S17: BIP360 draft](https://raw.githubusercontent.com/bitcoin/bips/master/bip-0360.mediawiki).
- [S18: BIP361 draft](https://raw.githubusercontent.com/bitcoin/bips/master/bip-0361.mediawiki).

# NOR-28: binding an attack before randomized auditing

Applied study: [Compactification-Theory NOR-28 PR #196](https://github.com/MoralityLabAI/Compactification-Theory/pull/196). Continues the kernel-verified coordinate-audit counting line NOR-23, NOR-25, NOR-26 and NOR-27.

## Protocol order

An attacker fixes an altered-coordinate set A and publishes an abstract binding commitment C(salt,A). Only after this does an external auditor draw an independent random root and produce a set of examined coordinates Q(root). The attacker can later learn any function L(root), including the complete root, while remaining bound to A.

Theorem disclosure_after_commitment_cannot_change_detection shows that, for the same realized root and the same committed attack, the intersection-based detection decision is identical under any two subsequent leakage views. This is a pathwise nonanticipation property and does not assert that knowing the seed before commitment would be harmless.

The digest consistency theorem assumes an abstract binding property:

    C(salt1,A) = C(salt2,B) -> A = B

Under that assumption, two openings with the same commitment must identify the same attack. A changed attack must fail the original digest verification. These statements are logical consequences of binding and **do not establish SHA-256 collision resistance**.

If the attacker instead selects the changed future after seeing the actual complete audit schedule, the NOR-25 transcript-indistinguishability construction gives a changed target that matches every inspected exact value whenever an unchecked coordinate exists. A new commitment generated after this disclosure is outside the original commit-first protocol.

## Finite detection floor

For fixed blind attacks and a uniform reserve of eight probes following a risk-targeted prefix of eight, the inherited exact combinatorial minimum detection probability is

    1 - C(m-12,8)/C(m-8,8)

for a radius-four changed set and output length m. The NOR-26 arbitrary-prefix theorem remains available. Fresh audit entropy and HMAC-SHA256 are computational implementation assumptions rather than objects proved random by Lean.

## Kernel scope

The proof module at [MathCan/NOR28CommitBeforeEntropy.lean](../../MathCan/NOR28CommitBeforeEntropy.lean) includes:
- same digest implies original attack under an abstract binding hypothesis;
- changed attack cannot open a prior commitment;
- invariance of detection under arbitrary postcommit root-disclosure functions;
- detection equivalence for accepted reopened commitments;
- a schedule-visible alternate future with indistinguishable exact witness transcript;
- the inherited finite conditional missed-audit upper bound.

All are checked with the Lean 4.35 standard-library toolchain and an explicit axiom inventory; no Mathlib requirement. Real-world OS entropy, GitHub Actions job chronology, HMAC pseudorandomness, actual witness integrity and SHA binding are external assumptions in the applied experiment. The applied NOR-28 controlled procedure checks stage separation and independently replays archived evidence, without claiming a hardware or cryptographic proof.

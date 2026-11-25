# ACE-01 | Axiom choice elimination

Status: ACE-01 native Lean proof checked; ACE-03F executable ZF proof objects checked. Full conservativity and checker soundness remain open.
Base: f326fb3d1731f575dc6086e93f1bfa226445450c. Companion: research/rh_proof_distillation.

## Mathematical scope

Let phi be an arithmetic sentence and let ZFC derive phi. In ZF,
the definable inner class L satisfies each axiom instance of ZFC;
the natural numbers and their arithmetic operations agree with those of V.
Relativize the finite source derivation to L and use arithmetic absoluteness
to obtain a ZF derivation of phi. This is a metatheoretic argument, not a
Lean theorem in this branch. Shoenfield covers more general projective
statements, but the arithmetic case needs only the relevant absoluteness.
A systematic proof enumerator also terminates on this promise: check ZF
derivations by length and return the first whose conclusion is phi.
Without the promise, termination is not guaranteed.

For RH, use a ZF-provable equivalence to an arithmetic sentence, for example
an explicitly integer-valued criterion from Davis–Matiyasevich–Robinson
(1974). Lagarias' criterion is a useful intermediate, with a separate
formalization obligation for real exp/log and the arithmetic coding.
Source: https://arxiv.org/abs/math/0008177
RH equivalence references:
https://mathoverflow.net/questions/31846/is-the-riemann-hypothesis-equivalent-to-a-pi-1-sentence

Lean's native dependent type theory is a distinct object. Standard
set-theoretic models of its universe hierarchy use additional inaccessible
cardinal assumptions. See
https://github.com/leanprover/con-leche/blob/master/ConLeche/SetTheory/Core.lean .
A possible route is to identify an explicit background T and prove that
L inherits T, then eliminate AC relative to T. This cannot be reported as
a bare ZF proof unless the additional strength has also been eliminated.
The certification of the native RH theorem is documented at
https://leanprover-community.github.io/blog/posts/riemann-hypothesis/ .
Candidate infrastructure:
https://github.com/05-02-07/lean-constructible-universe .
Neither the full constructible-universe implementation nor RH proof
translation has been audited in ACE-01.

## First elimination pattern

For any relation R and finite list xs, if every member of xs has some
R-witness, there exists a same-length, pointwise-aligned witness list.
Proof: induct on xs; eliminate the existential for the head, apply the
induction hypothesis to the tail, and cons the resulting witnesses.
This is a proposition-level construction; it does not extract a computable
selector from arbitrary Prop-valued existence proofs into Type.
The Lean module MathCan/ACEFiniteChoice.lean states a comparison with
global Classical.choose and a replacement of the same proposition.
It deliberately does not assert general object-theory conservativity.

## Executable experiment

The finite Boolean-matrix gym simulates a compressed finite-choice rule.
The source certificate names a trusted instance and the macro; its
premises are verified by scanning every row for a 1. The compiler emits
the first valid column per row. The target checker independently accepts
only explicit witnesses that satisfy the same trusted matrix. Instance
IDs bind certificates to the caller's instance; they are not cryptographic
hashes. JSON input is expected; no general proof language is implemented.
There is no choice axiom in the JavaScript macro itself. The toy macro
models finite witness selection, not full ZFC choice.

Actual results from running the JavaScript functions before committing
their serialized source: 689 exhaustive matrices (dimensions 0..3);
192 stress matrices across seeds 109,113,127; all 589 satisfiable cases
compiled and checked; all 292 unsatisfiable cases rejected; 8,508
malformed or corrupted checks rejected (including 12 malformed instance
checks). See finite_choice_receipt.json for counts and probe accounting.
This is a deterministic smoke test, not a learned benchmark or evidence
of arbitrary axiom elimination.

Source validation 51,303 predicate probes; compiler search 43,263;
independent successful target verification 6,223. Input shape validation,
negative controls and wall time are not included in these probe totals.
The compiler intentionally repeats source validation; direct greedy
search has the same selection algorithm. There is no efficiency claim.
Record certificate bytes with a fixed encoding and shared input costs
in future comparisons.

Replay with Node 22 and the repository's pinned Lean toolchain:
```sh
node research/ace/finite_choice.mjs > /tmp/ace-replay.json
diff -u research/ace/finite_choice_receipt.json /tmp/ace-replay.json
lake env lean MathCan/ACEFiniteChoice.lean
```

The Node wrapper and native Lean file have not been executed in the
authoring environment; the JavaScript functions themselves were tested.
Expected axiom report: globalViaChoice depends on Classical.choice;
finiteChoice, alignedMap, globalWithoutChoice have no axioms.
Require actual kernel output before marking LEAN-CHECKED.

## Registered next gates (not run)

ACE-02: staged in [ACE02_ARITHMETIC_TRANSPORT.md](ACE02_ARITHMETIC_TRANSPORT.md). Explicit first-order syntax with de Bruijn scopes, isomorphism-based semantic transport and assignment locality; 2,304 finite formula checks passed. Lean kernel and standalone CLI replay remain pending.
ACE-03A: staged in [ACE03A_RELATIVIZATION.md](ACE03A_RELATIVIZATION.md). Generic class semantics and a restricted proof compiler, 3,840 compiled proofs checked. ACE-03B: staged in [ACE03B_ZF_INTERFACE.md](ACE03B_ZF_INTERFACE.md). ZF/ZFC schema encodings and certificate-gated proof translation; 1,920 axiom encoding comparisons passed. ACE-03C: [class closure certificates and pinned upstream audit](ACE03C_CLASS_CLOSURE.md). Five conditional derivations and four closed singleton-empty-class certificates checked. ACE-03D: [generated pure membership-language L predicate](ACE03D_CONSTRUCTIBLE_DEFINITION.md) with pinned formula and finite regressions. ZF adequacy derivation and L closure certificates remain due.
ACE-04: inspect inert Lean exports for choice dependency cones, distinguish
finite selection from well-ordering, quotient, and classical proof
dependencies. Prove the universe/background theory requirements for
the chosen native-to-object translation.
ACE-05: EvalMath gym with source proof, fixed statement hash, axiom budget,
target certificate, split by theorem family, and cost accounting;
baseline enumeration, deterministic finite-witness search, bounded
proof rewrite, learned proposal order with equal verifier budgets.
ACE-06: DataGoblin receipts with provenance, original and replacement
proof encodings, allowed and observed axioms, toolchain, resource budget,
verified outcome, and explicit nontermination/timeout labels.
ACE-07: only after the translation and equivalence obligations are
closed, try the RH arithmetic corollary. No paid compute is requested.

No RH choice-elimination result is claimed at this checkpoint.

Verification update: ACE-01 kernel and axiom report passed in run 45541612790. ACE-02 run 45542048477 failed on a reserved Lean keyword, renamed in 72807b8; fresh verification pending. See ACE-03B note for scope.

ACE-03E: [hierarchy closure and bounded induction certificates](ACE03E_HIERARCHY_CLOSURE.md). Fifteen checked object derivations, including exact Def existence/uniqueness and conditional L transitivity. ACE-03F: [finite witnesses and closed L certificates](ACE03F_FINITE_WITNESSES.md). Def inflation and transitivity of the pinned L predicate checked; closed relativized extensionality and foundation certificates accepted. ACE-03G: [initial stages and empty-set closure](ACE03G_INITIAL_STAGES.md), eight checked derivations and three closed relativized axioms. ACE-03H: [coherence, restriction, uniqueness and monotonicity](ACE03H_STAGE_COHERENCE.md), 13 checked derivations. ACE-03I: [general ordinal stage recursion](ACE03I_STAGE_RECURSION.md), 19 checked derivations including existence and uniqueness on ordinal domains. ACE-03J: [common stages and constructible pairing/union](ACE03J_CONSTRUCTIBLE_CLOSURE.md). Both closed axiom certificates accepted; ordinal comparability avoided by taking the union of successor indices. ACE-03K: [constructible Infinity](ACE03K_CONSTRUCTIBLE_INFINITY.md), checked omega limit, inductive stage and relativized Infinity. ACE-03L: [relative Power Set and least constructible ranks](ACE03L_CONSTRUCTIBLE_POWER.md). Closed Power Set import and general stage bounding checked. ACE-03M: formula-indexed reflection and Separation. Adequacy and checker soundness remain open.

Verification update: ACE-03E receipt and native Lean workflows both passed (45547032768, 45547032547). ACE-03F adds 14 object derivations and seven rejection controls; new workflow replay remains pending.

ACE-03G verification update: the preceding ACE-03F dedicated replay passed (45551886722). The authoring runtime accepted eight new proofs and nine rejection controls and reproduced the ACE-03D/F receipts. New CI replay remains pending.

ACE-03H: exact stage-graph coherence, restriction and same-domain uniqueness accepted; inflation discharged for within-graph and cross-graph monotonicity. Three independent goal checks and five negative controls passed. No new relativized axiom certificate; new CI pending.

ACE-03I: general stage-graph existence/uniqueness, ordinal stage-value existence/uniqueness and stage membership implying L accepted by executable ZF checker. Eight exact-goal checks, six negative controls; pinned L unchanged. New CI pending; uniform adequacy and checker soundness remain open.

ACE-03J: four split replays, finite relation program construction and exact common-stage/Def transfer. Five relativized fixed axioms now accepted by the executable checker. Previous ACE-03I CI passed. New CI pending; uniform adequacy and checker soundness remain open.

ACE-03K: six fixed axioms now have closed certificates in the executable checker. The Infinity import emitted 47,480 nodes. Three split replays passed; new CI pending. Uniform definition adequacy and formal checker soundness remain open.

ACE-03L: seven fixed axioms now have closed certificates in the executable checker. The Power Set import emitted 24,264 nodes. Three split replays passed; new CI pending. The least-rank functional bound applies to arbitrary ambient sets of constructible elements. Uniform definition adequacy and formal checker soundness remain open.

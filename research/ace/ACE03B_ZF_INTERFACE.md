# ACE-03B | Explicit set theory proof interface

Status: EXECUTABLE CHECKED. Constructible-universe certificates and
native Lean-to-set-theory translation remain open. This module is an
executable proof-checking prototype, not a kernel-formalized ZF proof
system. ACE-03A is retained as the pinned previous implementation.

## Object theory

zf_interface.mjs extends the de Bruijn language and natural-deduction
kernel from ACE-03A. The classical policy adds double-negation
elimination. Equality substitution accepts a formula with one extra
free variable, an equality proof of a=b and a proof of the formula
instantiated at a, and returns the formula instantiated at b.
Substitution is capture-safe under nested binders.

The set-theory axiom leaf is generated from a descriptor, never a
caller-supplied conclusion. Fixed axioms: extensionality, empty set,
pairing, union, power set, infinity, foundation. Separation and
replacement use explicit well-scoped pure set-language bodies with
0..32 free parameters, a practical prototype input bound. Separation
uses body indices x,p0,...; replacement uses y,x,p0,... . The replacement
antecedent requires a unique output for each member of the input set;
the consequent gives the exact image set. The extra parameter bound
does not represent a mathematical restriction on ZF itself.
The ZFC-only axiom is the standard choice-set principle for a
pairwise disjoint family of nonempty sets. ZF can establish its
equivalence with usual choice using disjoint tagging. The equivalence
proof is not implemented in this kernel. Empty set is a redundant
axiom in common presentations of ZF.

The finite semantics of the generated fixed axiom sentences were
compared with independently expressed set-membership conditions.
Schema formulas are compared with direct finite separation and
functional-image conditions; their body interpreter is shared.
Finite structures of size 1..3 are arbitrary relations, not ZF models.
No claim of satisfiability of the full axiom set in a finite model is
made. The tests check encodings, not the axioms' mathematical truth.

## Class interpretation and certificate gate

Source axioms may use ZF or ZFC. Target compiler policy permits
intuitionistic/classical logic or ZF and refuses ZFC. A fixed class
definition, when supplied, is a pure set-language formula with at
most one free variable. G(i) is interpreted by capture-safe
instantiation. The conversion rule requires identical syntax after
expanding the class abbreviation. It cannot simply assert G(i).
The compiler computes the exact relativized axiom from the source
descriptor, and checks the supplied certificate at depth zero and
empty hypothesis context in the target theory. Certificates for the
same goal cannot occur twice; missing or mismatched certificates
fail closed. A closed-import rule replays the proof from an empty
context even when inserted under a binder, preventing ambient
hypothesis leakage. No target axiom calls to choice are permitted.

The positive control is C(x) := x=x. The proof derives the
relativized empty-set axiom by eliminating an ordinary ZF empty-set
witness, using reflexivity for its class membership and a guarded
universal introduction for its empty-set property. The same
certificate is checked at depth zero and at open contexts.
It is repeated for each random trial; 384 passes are repetitions
of two insertion modes for one certificate, not 384 distinct axioms.
C=V does not provide a ZF proof of the relativized choice axiom.
No proof of choice in L is supplied.

The proof-checking implementation is not formally proved sound
or complete. It expects finite JSON proof trees and trusted policy
selection, has no cryptographic hashing or resource limit for
recursive syntax, and is not an untrusted-service boundary.
The regression suite is template-driven and cannot replace a
proof of all inference cases.

## Actual finite receipts

Three seeds 109/113/127, 64 trial structures per seed:
- 1,536 fixed axiom encoding comparisons, 192 separation and
  192 replacement encoding comparisons (1,920 total).
- 384 schema leaves checked; 1,920 translation attempts without
  certificates refused.
- 576 classical/equality proof compilations.
- 384 successful repeated total-class empty-set certificate
  insertion checks.
- 22 additional malformed/unauthorized/forged proof controls refused.
- 3,840 original ACE-03A proof translations replayed successfully
  under the extended checker.

The functions were executed in a JavaScript runtime before commit.
The exact committed JavaScript source and JSON receipts were fetched
and replayed in that runtime, with matching outputs for all four
ACE scripts. The finite_choice.mjs module export declaration had
to be removed for that function-wrapper replay; other three source
texts executed unchanged. Standalone Node CLI CI is not yet observed.
The new targeted ACE workflow checks all four receipts and Lean
axiom reports.

## Native Lean status

ACE-01 pinned head 70a0ab297c8bbfa7023d8b215c9823f155267175:
GitHub run 45541612790, job 138961229177, passed. Kernel log confirms
finiteChoice, alignedMap, globalWithoutChoice have zero axioms;
globalViaChoice has exactly Classical.choice.
https://github.com/patrickdugan/MathCan/actions/runs/45541612790

ACE-02 pinned head 29a8835807f072611e1a4d6bceef4dfa2a6c772c:
run 45542048477 failed at Lean parsing because scoped is reserved.
The resulting sorryAx reports are consequences of failed elaboration,
not acceptable certificates. Commit
72807b8d341f6b9902f6290255ca2e83a4c5c9cf renames it to wellScoped.
Fresh kernel check remains pending.
https://github.com/patrickdugan/MathCan/actions/runs/45542048477

ACE-03A mathematical workflow 45543599063 was queued when inspected.
No acceptance of the generic class lemma is claimed yet.
The revised workflow enforces absence of sorryAx and unexpected
Classical.choice in all three modules. It permits propext, which
is a separate foundational dependency, and reports actual axioms.

## Next gate ACE-03C

Define the candidate constructible class as an object-language
formula and give certified interpretations of specific axioms in L.
Start by pinning existing formal L infrastructure and auditing
its metatheory, universe levels, theorem statements and definitions.
Then produce reusable certificates for transitivity and extensionality,
empty set, pairing and union, before approaching separation,
replacement, the definable well-order and the choice-set axiom.
Relativized axiom proof objects must be discharged from target ZF
rather than inserted as assumptions. An independently verified
native Lean-to-object-theory interpretation is still required to
connect Alpoge's RH theorem. No claim of general axiom elimination,
an RH proof in ZF or a choice-free foundation for Lean follows.

Paid compute: zero.

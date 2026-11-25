# ACE-02 | Arithmetic semantic transport

Status: FINITE EXECUTABLE CHECKED; LEAN KERNEL PENDING. This is the
arithmetic semantic lemma toward L/V absoluteness. No constructible
universe or ZF proof calculus has been built at this checkpoint.

## Formal interface

MathCan/ACEArithmeticTransport.lean defines object syntax with de Bruijn
indices. Terms have zero, successor, addition and multiplication.
Formulas have falsum, equality, strict order, conjunction, disjunction,
implication and both quantifiers; negation is implication to falsum.
A sentence is a formula scoped at depth zero. Binding pushes the new
value at index zero and shifts prior values one position.

For arbitrary types A and B and arithmetic interpretations M,N,
an Iso supplies a map, injectivity, surjectivity, preservation of zero
and operations, and preservation/reflection of order. No PA axioms
are needed for the generic transport lemma. In particular this model
interface is not a claim that all such structures are arithmetic models
of PA. For a source valuation rho and target sigma related pointwise
by the map, the intended native Lean results are:

- push_transport: compatibility under extending assignments.
- eval_transport: evaluation of every term commutes with the map.
- sat_transport: satisfaction of every formula transports in both directions.
- sentence_transport: every closed sentence has invariant truth.
- push_local, eval_local, sat_local: agreement below the binder depth
  implies identical evaluation or logically equivalent satisfaction.
- sentence_assignment_independent: any assignments give the same
  truth for a well-scoped sentence.

Written proof: induction on term/formula trees. Atomic equality uses
injectivity; order uses its supplied iff. The quantifier cases use
surjectivity in the direction that needs preimages, eliminating the
existential witness into Prop. They need no selected inverse function.
Scope locality follows the same induction with the agreement bound
incremented at a binder. Print actual transitive axioms for each theorem
and reject Classical.choice and sorryAx; the intended proofs are
constructive. Kernel acceptance and exact axiom sets are pending.

## Executable check

arithmetic_transport.mjs independently evaluates direct modular
arithmetic and finite operation tables after a nonidentity relabeling.
Three seeds (109,113,127), three domain sizes (2,3,5), 256 formulas per
seed and size, half closed and half open. Formula grammar depth 4,
term depth 3; assignments and permutations are seed derived. The
synthetic cyclic structures need not obey PA axioms.

All 2,304 formulas preserve truth and scope locality. There are 877
true and 1,427 false cases. 63 hand-coded binder checks, 10 malformed
scope checks, 36 corrupted-operation isomorphism rejections, 9 explicit
successor-mutation truth flips and 2 domain-extension truth flips passed.
Both evaluators explicitly bind variables; the target uses tables
and quantifies over the supplied domain. The check is finite regression,
not a proof of unbounded arithmetic truth or absoluteness. Actual
receipt: arithmetic_transport_receipt.json.

An injective operation-preserving inclusion of the one-point constant
zero structure into a two-point constant zero structure preserves
atomic formulas. The universally quantified sentence "all x, x = 0"
changes from true to false. The existential "some x, x != 0" changes
from false to true. This is a proper substructure counterexample for
general first-order structures, not a pair of ZF universes or PA models.

Replay:
```sh
node research/ace/arithmetic_transport.mjs > /tmp/ace02.json
diff -u research/ace/arithmetic_transport_receipt.json /tmp/ace02.json
lake env lean MathCan/ACEArithmeticTransport.lean
```

JavaScript functions were executed in the authoring runtime before
serialization to the committed Node source. Standalone Node and Lean
replays are still due. Lean 4.35.0 is the pinned repository toolchain.

## ACE-03 gates

1. Build a first-order set-language AST, capture-safe restriction to a
   definable class, and a proof kernel with explicit schemas and
   independently checked inference rules.
2. Prove relativization of satisfaction and derivations. Formalize
   the necessary L construction and proofs of every ZFC schema
   instance; avoid treating satisfaction for the entire ambient
   universe as a definable truth predicate inside ZF.
3. Connect the natural-number objects of L and V, prove the actual
   isomorphism hypotheses, and derive the syntactic conservativity
   transformation for each fixed arithmetic sentence. Keep
   assumptions about the metatheory and object theory separate.
4. Pin an RH arithmetic criterion and establish its equivalence in the
   chosen object theory. Audit the native Lean universe translation
   separately, since the present transport theorem is generic semantic
   invariance and supplies no translation of Alpoge's proof.

No paid compute used. No trained reasoner, ZF derivation or RH
choice-free certificate produced in ACE-02.

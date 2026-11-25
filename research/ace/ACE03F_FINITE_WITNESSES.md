# ACE-03F | Explicit finite witnesses and closed L certificates

Status: fourteen closed derivation trees accepted by the executable
ACE ZF checker. Def inflation is discharged; the exact pinned L
predicate is proved transitive by composition with ACE-03E.
The checker accepts two closed relativized ZF axiom certificates
(extensionality and foundation). Object-kernel soundness and uniform
adequacy of the L definition still require formal verification.
No full ZFC interpretation or RH result is claimed.

## Finite witnesses

The proof generator uses the exact subformulas of
constructible_definition.mjs; the default formula generator output
and pinned L_formula.json remain unchanged. The newly exported
subformulas expose singleton, unordered pair, tuple, inductiveness,
agreement, membership-relation, entry and program/slice witnesses.

finite_witnesses.mjs emits pure set-language natural deduction trees
from a named-variable builder. The builder is untrusted; the separate
executable checker checks all conclusions at empty hypotheses and
free-variable depth zero using the ZF policy.

The witness construction proves:
- existence and injectivity of the exact Kuratowski ordered pairs;
- existence of unary and binary function graphs with the required
  values (binary domain elements must be distinct);
- existence of the least inductive set omega, by Separation on an
  inductive set and the uniqueness of empty sets and successors;
- existence of distinct zero and its successor, and of their
  two-element successor, with the stated finite-domain properties.

For the exact atomic membership relation on n-coordinate tuples,
take B = union {A,n}. Every entry of a tuple graph is an ordered pair
whose first coordinate belongs to n and whose second belongs to A.
Graph functionality ensures that the witness supplied by the range
condition agrees with that entry. Both coordinates belong to B.
Every Kuratowski pair of such coordinates is a subset of P(B),
hence belongs to P(P(B)); each tuple graph therefore belongs to
P(P(P(B))). Separation on this bound yields the exact atomic
membership relation, without assuming that the class of tuple graphs
is itself a set. The relation is specified by the pinned relMem
formula rather than an external truth oracle.

## Inflation proof

Suppose A is transitive and x belongs to A. Construct n=2, m=1,
coordinate zero z and coordinate one o in the least inductive set.
The one-entry program is the unary graph {<z,r>} where r is the
atomic membership relation on coordinates z,o of tuples in A^n.
Use a binary base tuple assigning x to both coordinates.

For each y in x, transitivity places y in A. Construct the tuple
with values y,x. Its membership-relation witness is immediate and
it agrees with the base assignment at every coordinate other than
zero. Conversely, an accepted slice supplies a tuple s with
value y at zero, satisfying the atomic membership condition. The
functionality of s identifies the membership witness's first value
with y. Agreement at coordinate one and base functionality identify
its second value with x. Equality substitution gives y in x.

These two implications certify the exact slice condition. The
program's single index has an admissible atomic membership entry,
and all ordinal, graph, validity and slice witnesses are supplied
explicitly. Introducing the existential witnesses proves D(A,x).
The exact Def(A,B) membership equivalence now gives x in B.

The closed inflation theorem is syntactically equal to the premise
of both ACE-03E conditional transitivity theorems. Modus ponens
produces closed proofs of stage-graph transitivity and of
forall x, L(x) -> forall y, y in x -> L(y).
For the latter, the conclusion is independently reconstructed from
the pinned definition and compared against the checked goal.

## Closed L axiom certificates

Expand the class abbreviation G as the exact pinned L predicate.
The guard-conversion proof derives the generic transitivity property
from the pure closed L transitivity theorem. Combining it with
ACE-03C's conditional derivations yields certificates for the
relativized extensionality and foundation axioms.

The ACE compiler accepts both in a translation of their conjunction
from its ZFC source policy into its ZF target policy with class
definition L. The source has three proof-tree nodes and the emitted
target has 5,898 nodes. This is a checked two-axiom example;
the source example itself does not use the choice axiom.

No stage recursion existence is assumed in the transitivity
argument. It only concerns the stage graphs that satisfy the pinned
definition. In particular, these results alone do not establish the
nonemptiness of L. Uniform correctness of the definition relative
to the usual constructible hierarchy remains a separate task.

## Receipts and trust boundary

14 checked derivations, including 2,556 nodes for inflation,
2,806 for stage transitivity and 2,897 for pure L transitivity.
The relativized extensionality and foundation proofs have 2,952
and 2,943 nodes respectively. Seven negative controls check
the missing inflation proof, a mismatched premise, a disallowed
axiom policy, use of the wrong class definition, and attempts to
import uncertified choice, pairing and empty-set axioms.

Proof sizes are compact JSON tree byte counts, with repeated
formulas. They are not wall-time measurements or compressed
certificate sizes. The proof objects are generated on replay, not
stored as separate megabyte-scale files.

The preceding ACE-03E dedicated and MathCan workflows passed:
https://github.com/patrickdugan/MathCan/actions/runs/45547032768
https://github.com/patrickdugan/MathCan/actions/runs/45547032547

The new derivation trees were executed and checked in the authoring
JavaScript runtime. Native Node CI for this new checkpoint is pending.
The earlier native Lean theorems do not certify soundness of this
object checker. No paid compute was used.

Replay:
  node research/ace/finite_witnesses.mjs > /tmp/ace-f.json
  diff -u research/ace/finite_witnesses_receipt.json /tmp/ace-f.json

## ACE-03G gate

Prove existence and exact values of the zero-stage and one-stage
graphs directly, obtain L(empty), and discharge empty-set closure.
Then prove existence and coherence of general stage graphs via a
set-coded transfinite recursion construction, derive monotonicity
and pair/union closure, and continue the remaining axiom certificates.
Keep uniform coding adequacy and formal soundness of the proof
checker as explicit obligations.

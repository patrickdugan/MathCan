# ACE-03J | Pairing and union in the pinned constructible class

Status: closed object-language pairing and union certificates accepted by
the executable ZF checker and imported through the ZFC-to-ZF compiler.
These are two additional relativized fixed axioms for the exact pinned
L predicate. Formal soundness of the checker and uniform adequacy of the
constructible definition remain open.

## Common ordinal stage

If L(x), L(y), unpack their actual witness histories and ordinal indices
a,b, with successor domains d=a+1 and e=b+1. The successor of an ordinal
is an ordinal, and a binary union of ordinals is an ordinal using the
pinned characterization: transitive set of transitive sets. Construct
c=d union e by Pairing and Union; c contains a and b. This avoids needing
a separate ordinal comparability theorem.

Use ACE-03I stage-value existence at c and ACE-03H cross-history
monotonicity (with the ACE-03F inflation theorem discharged). Both x
and y belong to the resulting stage value. Its transitivity follows
from the closed stage-transitivity proof. The common-stage theorem
provides c, the exact stage-value witnesses, transitivity and both
membership proofs.

For any ordinal a and its successor b, coherence identifies the
predecessor value in the history at b with the value at a. Predecessor
uniqueness eliminates the alternate successor index, and the limit
branch contradicts the successor witness. Thus the value at b is
exactly Def of the value at a. If a subset satisfies the pinned
definability predicate over a stage, it belongs to the successor
stage and hence to L.

## Finite programs

The optional relation exports in constructible_definition.mjs expose
the exact subformulas without changing the default L AST. Extend the
existing membership relation construction by Separation on the same
iterated powerset bound for equality, complement and existential
cylindrification. Intersection is Separation on its first operand.
The finite graph append theorem constructs a new Kuratowski entry and
proves it leaves old values unchanged; Foundation excludes self
membership of the old domain. Starting from an empty graph and
appending entries at finite ordinals in omega constructs the required
finite tuples and finite relation histories. The ternary tuple smoke
theorem has a weaker conclusion with existential index witnesses;
the actual pair and union proofs use the explicit zero and successive
ordinal witnesses and all exact program and slice formulas.

Pairing uses arity three and a six-instruction program on coordinates
0,1,2 (distinguished variable, first parameter, second parameter):
  eq(0,1), eq(0,2), neg(0), neg(1), and(2,3), neg(4).
For a set A containing x,y, the base assignment is (x,x,y).
The last relation accepts precisely tuples satisfying coordinate-zero
equality to at least one parameter. A tuple with coordinates (u,x,y)
exists whenever u belongs to the ambient pair; membership in the
relation follows from the equality witness. Conversely, an accepted
slice supplies values at zero and both parameters, using the
agreement formula and graph uniqueness. Classical disjunction of
the atomic relation tests recovers u=x or u=y. This certifies the
exact slice for the ambient pair, hence D(A,{x,y}).

Union uses arity three and a four-instruction program:
  mem(0,2), mem(2,1), and(0,1), exists(2,2).
For a transitive A containing x, the base is (x,x,x). Given u in
union(x), the witness t in x and u in t both belong to A by
transitivity. Construct tuples (u,x,x) and (u,x,t). The second
belongs to the intersection and agrees with the first outside
coordinate 2, so the first belongs to the projected relation.
It agrees with the base outside coordinate zero. Conversely the
accepted slice supplies a tuple and a projection witness; agreement
and functionality recover u, x and the witness value t, and the
two membership relations give u in t in x. This certifies the
exact slice for the ambient union.

Every graph, relation and slice witness is discharged from ZF
axioms and schemas; there is no semantic-oracle proof rule.

## Relativized axioms

Construct an ambient pair using Pairing, then apply the common-stage
and finite pair definability results and the successor Def theorem
to show the pair belongs to L. For an ambient union use a single
stage containing x, its transitivity, the finite union program
and the successor Def theorem.

The pure class closure proofs have 19,903 and 11,522 proof-tree
nodes, respectively. Definitional guard conversion is checked
against the exact pinned L formula. The generic class-to-axiom
derivations from ACE-03C then supply the relativized Pairing and
Union certificates (the latter also uses closed L transitivity).
The compiler accepts each as a one-node ZFC source axiom under
the ZF target policy, emitting 19,929 and 14,484 nodes respectively.
The certificates themselves have 19,928 and 14,483 nodes.

There are now five fixed axioms certified in this executable
interface: extensionality, empty set, foundation, pairing and union.
No choice-using source proof was translated in this experiment.

## Replay and scope

The four independent replay parts are finite (10 checked proof
trees, including the repeated value-domain lemma), stage (8),
pairing and union (each checks the closure through a compiled
axiom certificate). Six exact-goal comparisons and nine rejection
controls passed across those parts. The alternative-class control
also independently compares expanded syntax; malformed conversion
tests use a deliberately unrelated empty-set proof. They do not
constitute a separate full replay of a large genuine axiom
certificate under an alternate class definition.

The first combined authoring-runtime replay exceeded its execution
timeout; the four smaller replays passed and have individual
receipts. The committed script and CI use separate parts to avoid
this issue. Proof byte sizes count repeated syntax in uncompressed
trees. The exact unary L formula is unchanged. New CI remains
pending. Previous ACE-03I dedicated and MathCan workflows passed
(45556029136 and 45556030938). No paid compute used.

Replay:
  for part in finite stage pairing union; do
    node research/ace/constructible_closure.mjs "$part" > "/tmp/ace-$part.json"
    diff -u "research/ace/constructible_closure_${part}_receipt.json" "/tmp/ace-$part.json"
  done

## ACE-03K gate

Prove that the least inductive set is an ordinal, identify the finite
ordinal values of the stage history and construct an inductive set
inside L. A useful route is the stage omega: prove n belongs to a
finite successor stage by induction, then show omega is a definable
subset of L_omega (requiring an explicit program for the ordinal
predicate). Alternatively show L_omega is inductive by proving
successor closure at its finite stages, and prove L_omega itself
belongs to L_(omega+1) via the universally true subset program.
Then discharge the relativized Infinity axiom. Power Set, Separation,
Replacement, Choice, uniform adequacy, formal checker soundness and
native Lean/RH translation remain outstanding.

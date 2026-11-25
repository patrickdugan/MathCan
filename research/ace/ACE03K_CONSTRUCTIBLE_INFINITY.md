# ACE-03K | Infinity in the pinned constructible class

Status: closed relativized Infinity certificate accepted by the executable
ZF checker and imported through the ZFC-to-ZF compiler. The exact L AST
is unchanged. Formal checker soundness, uniform definition adequacy,
and native Lean/RH translation remain open.

## Finite definability programs

For a transitive A and x in A, the successor x union {x} is definable
over A by u in x or u=x. The proof constructs a two-coordinate base
assignment (x,x) and six relations:
  mem(0,1), eq(0,1), neg(0), neg(1), and(2,3), neg(4).
Transitivity ensures each member of the ambient successor belongs to
A. The finite graph and relation existence lemmas from ACE-03J give
the witnesses. Membership in the last slice implies the disjunction
using atomic truth, graph functionality and classical logic. The
checked theorem is precisely that the ambient successor satisfies the
pinned D predicate. No formula syntax or primitive changed.

For every A, D(A,A) holds. If A is empty, use the first branch of D.
Otherwise choose a single existing member as base assignment by
existential elimination. The one-instruction program eq(0,0) accepts
every one-coordinate tuple. The slice agreement condition is vacuous
off the distinguished coordinate. Every member of A has such a tuple,
and the slice formula explicitly restricts membership to A.
This proves self-definability without an additional axiom.

## Ordinality and limit property of omega

Given the exact least-inductive-set predicate Omega(w), separate
c={x in w : Ord(x) and x subset w}. The empty set satisfies both
conditions. If x belongs to c, w supplies its successor y in w;
ordinal successor closure gives Ord(y), and the explicit successor
membership characterization gives y subset w. Thus c is inductive.
Leastness of w gives w subset c, hence w is transitive and all its
members are transitive. This establishes the pinned ordinal predicate.
If w were the successor of i in w, inductiveness would give a
successor j of i in w. Successor uniqueness gives j=w, contradicting
Foundation's exclusion of self membership. Thus w satisfies the
exact no-predecessor limit condition.

## Limit-stage characterization and inductiveness

For an ordinal b with no immediate predecessor, and its exact
stage witness W(b,r), the limit stage rule and overlap coherence
prove:
  x in r iff exists i in b, exists s, W(i,s) and x in s.
The forward direction takes an earlier value from the original
history and uses general stage existence and coherence to transport
it to W(i,s). The reverse direction follows from cross-history
monotonicity. No independent textbook interpretation of W is assumed.

Let w satisfy Omega and r satisfy W(w,r). The empty set z and its
successor j belong to w. Stage existence at z and j, the empty branch
of D and successor Def place z in the stage at j; monotonicity puts z
in r. For x in r, extract i in w and an earlier transitive stage a
containing x. The ambient successor y of x satisfies D(a,y) by the
six-instruction program. Inductiveness of w supplies j in w with
Succ(i,j). The stage at j contains y by successor Def; the limit
membership characterization then puts y in r. This proves Ind(r).

Every ordinal stage is itself in L, by D(A,A) and the ACE-03J
definable-subset transport theorem. In particular r=L_w satisfies
L(r) and Ind(r). General ordinal stage existence and Omega existence
supply the closed existential witness.

## Relativized Infinity

For an arbitrary guard G, transitivity and existence of a guarded
ambient inductive set imply relativized Infinity. The empty and
successor witnesses lie in G by transitivity. The universally
quantified defining properties of empty and successor restrict to
guarded variables. This generic implication has 61 proof nodes.

Instantiate G with the exact pinned L formula, discharge class
transitivity using ACE-03F, and use the closed inductive-set
existential. The compiler accepts the one-node ZFC source Infinity
axiom with the ZF target policy and emits 47,480 proof-tree nodes.
The certificate itself has 47,479 nodes and 50,795,540 compact JSON
bytes, counting repeated syntax. No choice-using source derivation
is translated by this experiment.

## Replays

Three independently executed parts:
- finite: successor definability 3,397 nodes, self-definability 1,647.
- stage: omega ordinal 394, omega limit 129, limit-stage membership
  8,609, omega stage inductive 33,251, ordinal stage constructible
  6,713 nodes.
- infinity: generic implication 61, closed inductive-set witness
  44,503 (individually checked during development), compiled Infinity
  target 47,480 nodes.

Eight independently reconstructed exact-goal checks and five negative
controls across the three parts passed. The negative controls reject
incorrect theory policies, missing axiom certificates and malformed
guard conversion. The wrong-class expansion is separately checked
syntactically, rather than replaying the large certificate under an
alternate class definition. The proof trees were executed in the
authoring runtime, and the three receipts record actual results.
Native Node CI for this checkpoint remains pending.

Replay:
  for part in finite stage infinity; do
    node research/ace/constructible_infinity.mjs "$part" > "/tmp/ace-k-$part.json"
    diff -u "research/ace/constructible_infinity_${part}_receipt.json" "/tmp/ace-k-$part.json"
  done

## Next gate ACE-03L

Power Set in L: for a constructible x, collect the constructible
subsets of x by ambient Separation on P(x). Bound their stage ranks
using Replacement and a common ordinal bound, so the relative powerset
is definable over a single stage. Construct an explicit finite program
for the subset predicate, then discharge the relativized Power Set
axiom. General Separation and Replacement schemas need further
reflection/bounding arguments. Choice still needs a canonical
constructible well-order. Uniform adequacy and formal checker soundness
remain separate gates. No paid compute.

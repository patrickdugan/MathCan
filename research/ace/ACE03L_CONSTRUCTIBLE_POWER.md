# ACE-03L | Relative Power Set and least constructible ranks

Status: the executable object-language checker accepts the closed
relativized Power Set certificate under its ZF target policy.
All three authoring-runtime replay parts passed. The pinned unary L
formula is unchanged. Formal soundness and uniform textbook adequacy
are still open.

## Ordinal comparison and least stage ranks

Use the pinned Ord predicate (transitive set of transitive sets).
Bounded induction on an ordinal's successor proves trichotomy:
a in b, a=b, or b in a, for ordinal a,b. At the induction step,
if b is not in a, the predecessor comparisons imply a subset b:
for x in a, the alternatives x=b and b in x both contradict that
assumption by transitivity. If b is also a subset of a, Extensionality
gives equality. Otherwise Separation forms b minus a; Foundation
supplies a minimal member y of that difference. Transitivity of b
and minimality give y subset a. Comparing each x in a with y, the
alternatives x=y and y in x contradict y not in a, so a subset y.
Thus y=a and a in b.

For the exact stage witness W(a,r) from ACE-03I, define
  Appears(x,a) := Ord(a) and exists r, W(a,r) and x in r.
  Rank(x,a) := Appears(x,a) and
               forall i in a, not Appears(x,i).
Unpack L(x) to get one witness a and its successor domain d.
Separate the indices satisfying Appears(x,i) inside d. The set is
nonempty because a is an element. Foundation yields a minimal
element b; transitivity of d ensures every predecessor of b also
belongs to d, so minimality proves Rank(x,b). Ordinal comparison
proves uniqueness by excluding the two strict-membership cases.
This is the least stage of appearance (not the ordinary von
Neumann rank).

## Bounding arbitrary sets of constructible objects

Define RankSucc(x,j) to mean there is a least appearance rank a
with Succ(a,j). For each x satisfying L this relation has exactly
one value by rank and successor uniqueness. If every member of an
ambient set S satisfies L, Replacement collects the successor ranks
into R. Each member of R is an ordinal. The union c of R is an
ordinal: membership in that union supplies a containing ordinal;
its transitivity and transitivity of its members give the two
conditions of Ord(c). For every x in S, its rank a is in its
successor j in R, hence a in c. Stage existence at c and
cross-history monotonicity imply x in its value r. The checked
conclusion is
  forall S, (forall x in S, L(x)) ->
    exists c,r, Ord(c) and W(c,r) and S subset r.
No choice axiom is used; the Replacement antecedent is proved
functional. The set S itself need not satisfy L.

## Explicit subset program

For transitive A containing x, the set p characterized by
  y in p iff y in A and y subset x
is definable over A. The program uses three coordinates, with base
(x,x,x), and six relation instructions:
  mem(2,0), mem(2,1), neg(1), and(0,2), exists(3,2), neg(4).
This encodes the absence of a member v of coordinate-zero y
outside coordinate-one x. The proof constructs actual graph
witnesses using ACE-03J finite-program lemmas. If y is in p, use
tuple (y,x,x); any bad projection witness would have a member of y
outside x, contradicting the subset hypothesis. Conversely, the
accepted slice supplies y and x coordinates. If v is in y but
not x, transitivity puts v in A. Tuple (y,x,v) supplies a bad
projection witness and contradicts the last complement relation.
Classical double-negation elimination gives the ambient subset
condition. The exact pinned D(A,p) then follows from the checked
program and slice.

## Relative powerset closure and axiom

Use ambient Power Set and Separation on the pinned L predicate
to obtain p with
  y in p iff L(y) and y subset x.
For constructible x, form S=p union {x}. Every member is
constructible. The stage-bound theorem gives a transitive stage A
containing all of S. Every element of A satisfies L, so the two
characterizations of p, by L and by A, are equivalent. Apply the
subset program and successor Def transport to derive L(p).

For an arbitrary guard G, assume transitivity and the exact
relative-powerset closure. If y satisfies G, every member of y
satisfies G by transitivity, so its guarded subset condition is
equivalent to its ambient subset condition. The generic theorem
derives the relativized Power Set axiom. Convert G to the pinned L
definition and discharge both premises using the already checked
transitivity and the new closure proof. Compile a one-node source
Power Set axiom under ZF policy; the target has 24,264 proof nodes.
The certificate has 24,263 nodes and 26,235,771 compact JSON bytes.

## Actual receipts and scope

Three replay parts checked:
- finite: relative_power_definable, 4,194 nodes.
- ranks: nine derivations, including ordinal comparison (527),
  least rank exists uniquely (737), successor rank totality (906)
  and stage bound (8,882).
- power: ambient relative powerset (45), generic implication (49),
  pure closure (21,299 nodes, checked during construction), and
  the axiom import (24,264 target nodes).

Eight independent exact-goal comparisons and six negative controls
passed. The alternate class expansion is tested syntactically;
the malformed guard proof uses an unrelated empty-set axiom.
All new parts compared generated L syntax to L_formula.json.
The initial generic axiom-builder attempt had an unbound variable
caused by selecting the body of an existential instead of the
existential formula itself; the corrected builder passed.
The three authoring-runtime receipts are pinned; Node CI for the
new checkpoint remains pending. Previous ACE-03K dedicated and
MathCan workflows both passed (45565329377, 45565331269).
No paid compute. The source axiom in the translation does not
itself use choice.

Replay:
  for part in finite ranks power; do
    node research/ace/constructible_power.mjs "$part" > "/tmp/ace-l-$part.json"
    diff -u "research/ace/constructible_power_${part}_receipt.json" "/tmp/ace-l-$part.json"
  done

## ACE-03M gate

Separation: develop formula-indexed reflection certificates. Given a
finite collection of object formulas and parameters, use the least
constructible-rank functional bound to bound witnesses for the
existential subformulas at each stage. Iterate stage enlargement
through omega and use limit-stage membership, monotonicity and the
finite Tarski-Vaught argument. A uniform object-language finite
program compilation and adequacy theorem will be needed to turn
the reflected formula into the exact D witness for the separated
subset. Keep the full separation schema distinct from any finite
instances checked first. Replacement in L and canonical well-order
for Choice remain open, as do formal checker soundness and native
Lean/RH translation.

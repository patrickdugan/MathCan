# ACE-03E | Object-theory closure and transfinite induction

Status: 15 closed derivation trees accepted by the executable ACE ZF
checker. Three independent exact-goal comparisons and five negative
controls pass. Object-kernel soundness is not yet formally proved.
No unconditional L transitivity, full ZFC interpretation, or RH
choice-elimination certificate is claimed.

## Exact definitions

The proofs use the generated pure membership formulas in
constructible_definition.mjs, not a replacement semantic predicate.
The generator optionally exposes its exact Val(f,i,r) and stageGraph(f,d)
subformulas. Its default output and pinned L_formula.json are unchanged.
hierarchy_closure.mjs is a named-variable proof builder that emits
de Bruijn natural-deduction proof trees; all trees are independently
replayed by the existing checker at depth zero, empty hypotheses,
pure set-language mode, ZF policy. Named hypothesis IDs are mapped
to context positions at emission; binders are fresh and substitution
is capture-safe. The builder itself is untrusted.

## Def existence and uniqueness

Let D(A,x) denote the generated definability predicate. Its empty
branch implies x subset A vacuously. In the program-witness branch,
open the finite program and its final slice witnesses. The slice
specification explicitly includes y in A on the right side of the
membership equivalence. Thus D(A,x) implies x subset A directly,
without invoking uniform adequacy of the program coding.

Apply Power Set to A. Apply the Separation schema on the resulting
powerset, using the exact D(A,x) as the body and A as parameter.
The resulting B has x in B iff x subset A and D(A,x), which is
equivalent to D(A,x). This proves the generated Def(A,B) relation
has a witness for every A. Extensionality gives uniqueness. These
are object proofs of totality and uniqueness of the pinned syntax,
not a completed uniform correctness proof relative to textbook Def.

Empty sets satisfy D(A,x) by its first disjunct. If Def(A,B), every
member of B is a subset of A and every empty set belongs to B.
If additionally A subset B, then B is transitive. A union of a
family of transitive sets is transitive by unfolding membership.

## Bounded induction

For any fixed pure set formula P with at most the kernel's allowed
number of parameters, the proof builder constructs a closed
instance of this principle:

For transitive d, if every i in d satisfies
  (forall j in i, P(j)) -> P(i),
then every i in d satisfies P(i).

Proof: use Separation on d to form the bad set of indices not
satisfying P. A bad element implies nonemptiness. Foundation
supplies a member i of the bad set with no bad member. Since d is
transitive, every j in i lies in d. If P(j) fails, j would be in the
bad set, contradiction. Classical double-negation elimination
gives P(j); the induction step gives P(i), contradiction.
The builder uses the exact negated property as a schema body.
Four instances were checked: transitivity, membership with one
parameter, the pinned L predicate, and stage-value transitivity.
This is a family of generated instances, not an internal universal
truth predicate or a theorem quantified over all object formulas.

## Stage graph and L transitivity

Define the remaining inflation premise I:
  forall A,B, Def(A,B) -> Trans(A) -> A subset B.

For a graph on a transitive index set d satisfying the exact stage
rules, use bounded induction with property
  P(i) := forall r, Val(f,i,r) -> Trans(r).
At a successor index, the predecessor value A is transitive by
induction, and I supplies A subset Def(A). Apply the proved
successor transitivity lemma. At a limit index, each member of the
stage belongs to an earlier stage; induction proves that earlier
stage transitive. The limit membership characterization then
places each member of that member in the limit stage. Exact graph
value uniqueness and equality substitution transport the result to
any value at the given index.

The pure object proof concludes I -> stage graph transitivity.
A separate proof gives transitivity of the successor of any
transitive set, using its explicit membership characterization.
Given L(x) and y in x, unpack the witnesses alpha,d,f,r of the
exact pinned L(x) formula. The ordinal alpha is transitive, so
its successor d is transitive. The conditional stage theorem
makes r transitive. Since x in r and y in x, y in r. Reuse the
same alpha,d,f,r to witness L(y).
The resulting proof is exactly
  I -> forall x, L(x) -> forall y, y in x -> L(y).

The premise I is still open at the object-proof level. The
mathematical argument is straightforward: if A is transitive
and x in A, x subset A, and the formula y in x with parameter x
defines x over A. The remaining construction must provide actual
finite program, graph and tuple witnesses for the pinned encoding.
Transfinite recursion existence and coherence of distinct stage
graphs, needed for full hierarchy monotonicity, are also open.
Neither is inferred from conditional transitivity.

## Receipts

15 checked derivations. The exact Def existence proof has 71
nodes, uniqueness 31. The stage induction instance has 72 nodes;
conditional stage transitivity 249, conditional L transitivity
340. The last uses 533,595 compact proof JSON bytes (the
tree repeats formulas). Counts are not runtime or memory metrics.
Three exact goals are rebuilt independently of the proof builder.
Five controls reject omitted inflation hypotheses, disallowed
theory policies and a mismatched premise.
See hierarchy_closure_receipt.json for each proof size.

The JavaScript implementation was executed in the authoring
runtime using fetched sources; native Node CLI CI is pending.
No native Lean module added. Earlier ACE-03B native Lean and
receipt CI passed; current branch CI is separate.
No paid compute.

Replay:
  node research/ace/hierarchy_closure.mjs > /tmp/ace-e.json
  diff -u research/ace/hierarchy_closure_receipt.json /tmp/ace-e.json

## ACE-03F gate

Construct a minimal explicit atomic-membership program witness
with two variables, one instruction, and a base assignment.
Prove the required standard finite ordinals, finite tuple space,
relation set and finite function graphs exist via ZF axioms and
schemas; discharge I. Then the existing proof gives unconditional
L transitivity, enabling the extensionality and foundation
certificates in ACE-03C. Keep recursion existence, empty-set
inclusion, pair/union closure and the full uniform adequacy
obligation separate.

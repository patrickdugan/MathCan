# ACE-03M | Formula-indexed witness bounds and conditional reflection transport

Status: closed executable ZF certificates for fixed-formula one-step
witness bounding, and checked conditional classical first-order
transport proofs. The full reflecting-stage existence theorem,
Separation schema and formal checker soundness remain open.
The pinned unary L AST is unchanged.

## Formula-indexed demand and least witness stages

Fix a pure membership-language formula phi(x,p0,...,p_(k-1)).
Use capture-safe relativization of all its quantifiers to the pinned
L definition. Write Phi for the resulting formula and W for the
exact stage-value witness from ACE-03I.

Define
  Demand(b,ps) := Ord(b) and exists r,
                  W(b,r) and exists x in r, Phi(x,ps).
  Min(b,ps) := Demand(b,ps) and
               forall i in b, not Demand(i,ps).

An L witness supplies Demand by unpacking its exact stage witness.
Given any demand index b, take its successor d, separate the demand
indices inside d, and apply Foundation to this nonempty set.
Transitivity of d proves minimality against every earlier index.
Ordinal comparison proves the minimum unique. This selects an
ordinal, not one of the potentially many set witnesses.

Define Selected(j,ps) as Ord(j) together with the disjunction:
- there is a minimum demand index i with Succ(i,j);
- there is no demand index and j is empty.

Excluded middle, minimum existence/uniqueness, successor
existence/uniqueness and Empty give exactly one selected ordinal
for each parameter assignment, even when no witness exists.
If an L witness exists, Selected guarantees a demand index in j.

## Finite parameter aggregation

For an ambient parameter set A, define a family of pure first-order
formulas indexed by the length of a fixed prefix ps. At full arity,
Agg(A,ps,j) is Selected(j,ps). Otherwise Agg asserts Ord(j) and
that j is precisely the union of the child ordinals:
  z in j iff exists i in A, exists k,
              Agg(A,ps+i,k) and z in k.

At each step, the child functionality theorem discharges the
Replacement antecedent for the exact child formula. Union of its
image exists and is ordinal by ACE-03L; Extensionality proves
uniqueness. Inductively compose the finite list of generated
derivations. This is host-level recursion over a fixed finite
arity producing object proof trees, not an internal assertion
about all formulas or all arities.

For every set A, the resulting top aggregate c is an ordinal.
Let r be its stage value. For each parameter tuple in A with an
L witness, descend the aggregate tree along the given tuple.
The selected demand index belongs to the leaf ordinal and hence
to every ancestor ordinal, including c. Cross-history
monotonicity transports the demand witness into r. The exact
conclusion is:
  forall A, exists c,r, Ord(c) and W(c,r) and
    forall ps in A^k,
      (exists x, L(x) and Phi(x,ps)) ->
      (exists x in r, Phi(x,ps)).

The bound does not assume A itself is constructible, and no
witness set selection or choice axiom is used. Empty parameter
sets and empty demands are permitted. For a given old stage
W(a,r), apply the bound to r and enlarge by taking the union of
the successor of a and the successor of the resulting bound.
Stage existence and monotonicity give a strictly larger stage
containing r with the witness property.

## Conditional finite Tarski-Vaught transport

For each quantifier occurrence in a fixed input formula, extract
a closure clause over all its in-scope variables. For an existential
with body psi, the clause asserts that whenever psi^L has an L
witness, it has a witness in the candidate domain A with the same
L-relativized truth. For a universal, use the counterexample body
not psi. Include all in-scope variables in the parameter arity,
even if some are unused. Nested clauses use the de Bruijn variable
ordering recorded by their occurrence paths.

Under A subset L and all extracted closure clauses, a recursive
proof generator establishes:
  forall parameters in A,
      phi restricted to A iff phi restricted to L.

Atomic and Boolean cases are direct. Existential forward transport
uses inclusion, and backward transport uses the witness clause.
Universal backward transport uses inclusion; forward transport
uses classical double-negation elimination, obtains an A
counterexample from the corresponding clause, and contradicts
the universally quantified A truth using the inductive
equivalence. The proof is checked under classical logic policy
with no set-theory axiom imports, as a conditional theorem
whose class predicate is expanded to the pinned L formula.
No internal global satisfaction predicate is introduced.

## Actual replays

reflection_bounds.mjs has five independently executed parts:
- membership: 8 proofs, one-parameter x in a, final bound
  10,333 nodes / 24,504,912 compact tree bytes.
- extension: 18,577 nodes / 33,693,244 bytes.
- two_parameter: x in a and x in b, 11,884 nodes /
  43,153,155 bytes.
- quantified: exists y, x in y and y in a, 10,333 nodes /
  41,044,033 bytes.
- closed: false (empty demand), 8,987 nodes / 14,860,776 bytes.

The generator accepts 0..3 parameters; replays cover 0..2 only.
The three-parameter case has not been checked. One initial combined
two-parameter quantified replay encountered an RPC error; separate
two-parameter and quantified fixtures succeeded. Individual proof
selection bounds peak materialized certificate size.

reflection_transport.mjs checks 5 derivations: 46, 333, 274, 122,
45 nodes. They cover existential, nested quantifier, mixed
connective, closed sentence and atomic cases. Independent finite
semantic regression uses 50 membership relations, 1,014 domain
inclusions, and 5,070 formula/domain cases. Closure clauses hold
in 4,717 cases; all 5,040 assignment truth comparisons for those
cases pass. There are 262 cases in which clauses fail and an
assignment exhibits disagreement. Finite relations are arbitrary
structures, not models of ZF. Empty candidate domains are included
as semantic regressions. The transport generator accepts up to
6 top-level parameters; tests cover 0..2, and the deepest
extracted clause in these tests has two parameters.

Across the split replays: 17 checked proof trees (12 bounds and
5 transport), 10 independently reconstructed final goals and
19 rejection controls (15 bound, 4 transport). Counts of compact
bytes include duplicated syntax and do not measure runtime or
compressed proof size. No new relativized axiom certificates.
Previous ACE-03L dedicated and MathCan workflows passed
(45570435907 and 45570433259). New CI pending; no paid compute.

Replay:
  for part in membership extension two_parameter quantified closed; do
    node research/ace/reflection_bounds.mjs "$part" > "/tmp/ace-m-$part.json"
    diff -u "research/ace/reflection_bounds_${part}_receipt.json" "/tmp/ace-m-$part.json"
  done
  node research/ace/reflection_transport.mjs > /tmp/ace-m-tv.json
  diff -u research/ace/reflection_transport_receipt.json /tmp/ace-m-tv.json

## ACE-03N gate

Combine finitely many extracted witness clauses at a single larger
stage by monotonicity and ordinal union. Define a canonical least
strict extension satisfying that finite conjunction, prove existence
and uniqueness using the formula-indexed least ordinal argument,
then construct its omega-length iteration by finite recursion and
Replacement (no dependent choice). Take the union of the increasing
ordinal sequence. Prove each finite parameter tuple at its limit
stage already lies in an earlier member stage; the successor
extension supplies the required witnesses at the limit. Apply the
conditional transport generator to conclude finite-formula reflection.

The subsequent Separation gate must compile fixed first-order
formulas into actual set-coded finite programs for the pinned
D predicate, proving slice adequacy for general formulas; the
current explicit programs cover only earlier selected operations.
Replacement and Choice remain to be proved. The bound generator's
arity cap must be lifted or replaced with set-coded tuple
aggregation to support arbitrary finite schema instances. Formal
checker soundness and native Lean/RH translation remain separate.

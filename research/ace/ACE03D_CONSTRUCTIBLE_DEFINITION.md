# ACE-03D | Explicit object-language definition of the constructible class

Status: GENERATED SYNTAX AND EXECUTABLE REGRESSION PASS. A written ZF
adequacy argument is supplied below; its derivations have not yet been
encoded and checked in the object proof calculus. No closed L axiom
certificate has been produced.

## Pinned definition

constructible_definition.mjs generates pure first-order membership
formulas by hygienic named-variable macros and compiles them to the
ACE de Bruijn AST. L_formula.json pins the complete generated L(x)
AST (compact JSON 53,323 bytes, excluding final newline).
The only free index is 0. The full tree has 6,969 nodes, 2,866 atomic
occurrences, 1,196 quantifiers and maximum binder depth 25.
There are no class guards or nonlogical constants in the definition.
The generator exports nine formulas with explicit arities.

### Set-theoretic primitives

Ordinal(a) is transitivity of a and of all members of a. In ZF,
Foundation and the usual ordinal comparison theorem identify these
with the von Neumann ordinals. Successor(a,b) says b = a union {a}
extensionally. Omega(w) says w is inductive and contained in every
inductive set; Infinity and Separation establish the standard omega.
The graph predicate uses Kuratowski pairs, exact domain membership,
and total unique values. Tuple(s,n,A) is a function from n to A.

### Definable subsets without a truth predicate for V

For a set A and positive finite ordinal n, use the set A^n of
assignments of n variables. An admissible program of positive finite
length m is a function f with domain m, whose value at each k in m
is a relation on A^n and is one of the following:

1. Atomic equality of two coordinates.
2. Atomic membership of two coordinates.
3. Relative complement in A^n of an earlier relation.
4. Intersection of two earlier relations.
5. Existential cylindrification of an earlier relation at a coordinate:
   include an assignment s if an earlier accepted assignment t agrees
   with s everywhere except possibly at that coordinate.

Each relation is specified extensionally by a pure set formula.
There are no opaque operation tags in the object formula; the five
cases form a disjunction, and predecessor references must lie in k.
All stages of a valid program are subsets of A^n by finite induction.

A subset X is definable over A iff it is empty, or there are positive
n,m in omega, an admissible program, and a base assignment b in A^n
such that X is the last relation's slice with coordinate zero varying
over A and the other coordinates fixed by b. The empty case covers
A empty, for which positive-arity assignments do not exist.

Written adequacy argument:
Every relation in an admissible finite program is definable by a
formula of the membership language, by induction on program index:
the atomic cases are immediate; complement, intersection and
cylindrification correspond to negation, conjunction and existential
quantification of the relevant coordinate. Fixing the remaining
coordinates gives a formula with parameters in A defining X.
Conversely, for any first-order membership formula with finitely
many variable names, rename as needed, take a finite n containing
all its variables (coordinate zero the distinguished variable),
and write it using equality, membership, negation, conjunction and
existential quantification. A postorder traversal builds a finite
program of the prescribed form, using Separation on A^n for the
relation at each step. For nonempty A, unused coordinates of the
base assignment can be filled with any single member of A; no
axiom of choice is required. The empty subset always has a
contradictory defining formula. Consequently these are exactly the
standard definable subsets of A with parameters from A.

ZF constructs A^n and the relevant subsets by its ordinary set
operations and Separation; all finite program witnesses are sets.
The equivalence is a mathematical argument in the intended
well-founded set-theoretic interpretation. A formal uniform
coding/induction proof inside ZF, including arbitrary internally
coded finite formulas in arbitrary models, remains an explicit
obligation. Finite JavaScript evaluation does not establish that
uniform object-theoretic adequacy theorem.

Def(A,B) says that B contains exactly these definable subsets.
Power Set and Separation give B, and Extensionality makes it unique.
The first-order definition quantifies over set-sized relations on
assignments, so no global truth predicate for V is introduced.

### Stage graphs

L(x) asserts that there exist an ordinal alpha, its successor d,
and a function f on d, with:
- For every successor index b = i+1 in d, f(b) = Def(f(i)).
- For each index b without an ordinal predecessor (zero included),
  f(b) is the union of f(i) for i in b.
- x belongs to f(alpha).

By the ZF transfinite recursion theorem, a unique such f exists for
each alpha, and transfinite induction identifies f(b) with L_b.
At zero the union is empty; at a nonzero limit it is the standard
union of earlier stages. Hence the intended unary predicate defines
the constructible class. This argument invokes the usual ZF recursion
theorem and the Def adequacy argument above. Neither has yet been
compiled into a checked object derivation.

## Next closure lemmas (written roadmap, not certificates)

Prove by transfinite induction that each stage is transitive and
increasing. If A is transitive then A is contained in Def(A):
every member x of A is a subset of A and is defined over A by
the membership formula with parameter x. Also Def(A) is transitive,
because its members are subsets of A and A is contained in Def(A).
Limit unions preserve transitivity and monotonicity. This gives T.

The empty set belongs to L_1. Pair closure follows by selecting
one stage containing both inputs (ordinal comparison and monotonicity)
and defining their pair over that stage. Union closure follows by
selecting a transitive stage A containing x; union(x) is a subset of A
defined over A by existence of a member of x containing the argument.
These establish the intended EC, PC, UC from ACE-03C once the stage
facts and definition adequacy have actual ZF proofs. No new class
axioms may be assumed in a closed certificate.

## Tests and receipt

Three seeds 109,113,127, 128 relation programs per seed; assignment
domains 0..3, widths 1..3, grammar depth 4. Independent recursive
formula and bottom-up relational evaluators agree on 1,862 assignments
and 1,862 parameter slices. There are 96 empty-domain programs;
their positive-arity assignment sets are empty. All 30 subsets of
domains of sizes 1..4 have explicit equality/parameter program
witnesses. Six invalid relation programs are rejected.
A concrete transitive hereditarily finite domain of size 12 checks
31 empty, ordinal, successor, Kuratowski pair and graph examples
(including partial, nonfunctional and stray-element graphs).
The full L/Def object formula is NOT evaluated in these finite
structures: finite domains have no standard omega, and a successful
test would not establish the intended infinite semantics.
Nine generated formula trees pass free-index and alpha-renaming
checks.

constructible_gate.mjs checks the pinned formula equals the generator,
20 class-abbreviation introduction/elimination checks over depths
1..4, five expansion checks under binders, rejects four prior
singleton-empty-class certificates under the new class definition,
and blocks eight uncertified fixed axiom imports.
It does not derive L-specific class closure facts.

The authoring JavaScript runtime executed the generator, finite
regressions and the gate logic before committing their outputs.
Native Node CLI and updated CI are due; modules expose their functions
without running their CLI when imported. The preceding ACE-03B
targeted workflow and MathCan mathematical checks both passed:
https://github.com/patrickdugan/MathCan/actions/runs/45543967919
https://github.com/patrickdugan/MathCan/actions/runs/45543967937
New CI adds both ACE-03D scripts to the receipt diff loop.

Replay:
```sh
node research/ace/constructible_definition.mjs > /tmp/ace-d.json
diff -u research/ace/constructible_definition_receipt.json /tmp/ace-d.json
node research/ace/constructible_gate.mjs > /tmp/ace-gate.json
diff -u research/ace/constructible_gate_receipt.json /tmp/ace-gate.json
```

Next: encode set-coded finite programs and transfinite recursion
lemmas as reusable object derivations; prove Def adequacy, then T,
EC, PC and UC for the pinned formula. Audit the unverified proof
checker independently before relying on it for a foundational claim.
No paid compute or RH proof translation.

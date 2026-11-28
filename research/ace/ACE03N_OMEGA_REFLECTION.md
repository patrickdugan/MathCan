# ACE-03N | Canonical omega iteration and modular reflection

Status: complete modular executable ZF proof chain for reflection of
one fixed quantified formula, exists x (x in p). All eight closed
dependencies and their exact interface formulas were separately checked,
as was a logical implication/application proof linking them. The fully
expanded single tree was attempted and hit a resource/RPC failure;
no monolithic replay is claimed. The pinned L formula is unchanged.
No new relativized ZFC axiom certificate in this checkpoint.

## Canonical simultaneous extension

For a finite nonempty list of witness clauses, define Good(a,b) by
Ord(b), a in b, and exact stage witnesses r=W(a),s=W(b) such that
each required clause holds from parameters in r to witnesses in s.
Given the strict stage-extension theorem for each clause, take the
maximum of their proposed ordinals using ordinal comparison.
At unequal ordinals, monotonicity transports the earlier witness
to the later stage. At equal ordinals, uniqueness of the exact
stage values transfers the clauses by equality substitution.
The combined extension exists without choosing set witnesses.

Define Next(a,b) as Good(a,b) and no earlier index i in b
satisfying Good(a,i). Given any eligible b, separate eligible
indices inside its successor; Foundation supplies a minimal
element and transitivity supplies the unrestricted earlier-index
minimality. Ordinal comparison gives uniqueness. Thus Next is a
pure fixed-formula functional ordinal step, strictly increasing.
For one clause the ACE-03M extension proof discharges the hypothesis;
the two-clause fixture still has both extension premises.

## Finite iteration and the endpoint set

For an arbitrary fixed pure binary relation R on ordinals, assume
the exact totality/uniqueness condition
  Ord(a) -> exists b, (Ord(b) and R(a,b)) and
                      forall c, R(a,c) -> c=b.
A history on a domain d is a function graph f on d whose values
are ordinals, whose value at zero is the initial ordinal a, and
whose values at successor indices obey R. No rule is needed for
other limit indices. Define Tight(a,n,v) by a history on the
successor of n having value v at n. Define End(a,n,v) by a history
on any transitive domain containing n having value v at n.

For n in omega, separate the indices satisfying the property:
there exists v with Tight(a,n,v) and every End(a,n,u) implies u=v.
The zero case appends the initial value to an empty graph. For the
successor step, use the tight history at n, the functional step to
obtain the new value, and the exact graph-append theorem. Previous
rules are preserved by the value equivalence on the old domain;
the new rule uses predecessor uniqueness. Any competing history
on a transitive domain containing the successor contains n, so the
induction hypothesis identifies its preceding value. Functionality
of R establishes uniqueness of the new endpoint. This proves the
separated subset inductive; leastness of omega proves the property
for all its elements. The proof also establishes transitivity of
each member of omega by a separate inductive subset.

Tight implies End because the successor of a transitive domain is
transitive and contains its predecessor. Hence End is total and
unique on omega. Replacement collects its values into a set Rng.
The initial ordinal lies in Rng, all its elements are ordinals, and
each v in Rng has an R-successor in Rng: take a witnessing index n,
its successor j in omega, a tight history at j, and use uniqueness
at n to identify the preceding endpoint. This is an omega iteration
by functional finite histories and Replacement. It uses neither
dependent choice nor an assumed infinite graph-selection function.

## Reflecting limit

For the canonical strictly increasing step, union the set Rng
to form lambda. Ordinality follows from the ordinal-family union
lemma. Each v in Rng lies in lambda because its strict successor
also belongs to Rng. If lambda were a successor of i in lambda,
choose b in Rng with i in b. Since b in lambda, successor membership
would imply b in i or b=i, contradicting Foundation. Thus lambda
satisfies the no-predecessor limit rule, and the initial ordinal
belongs to lambda.

Use the exact ordinal limit-stage membership theorem at lambda.
Each parameter in its stage value belongs to an earlier stage,
whose index is in some member of Rng. Monotonicity puts that
parameter into the stage at that member. A finite tuple fits in one
member stage by ordinal comparison and stage-value uniqueness.
The Rng successor of that member supplies all the requested witness
clauses. Monotonicity transports the witnesses to the lambda stage.
For zero parameters start directly with the initial ordinal.
This proves all the specified witness clauses at the limit stage,
conditional on the successor-closed range property.

## Exact modular composition

The independent interface builder in reflection_link.mjs constructs
the exact recurrence formula and eight expected closed theorem
statements. The fixed target formula is exists x (x in p). The
canonical, omega, limit, and base parts replay closed proof objects
and compare their conclusions byte-for-byte in compact JSON syntax
to those independently built interfaces. The base part includes
the exact omega existence and ordinal proofs, stage inclusion in L,
and the conditional Tarski-Vaught transport theorem.

The 96-node link proof, checked in the logic-only policy, is the
closed implication chain from these eight statements to
  forall a, Ord(a) -> exists lambda,r,
    Ord(lambda) and W(lambda,r) and a in lambda and
    forall p in r,
      (exists x in r, x in p) iff (exists x, L(x) and x in p).
The independent final-goal comparison reconstructs this formula
directly in de Bruijn syntax. A separate application check
instantiates the eight antecedents in an explicit closed-formula
context and obtains the same conclusion. Under ordinary
implication elimination/cut, the independently checked closed
dependencies discharge that context. This is a modular proof
certificate, not a single replay of an expanded proof tree.
Dropping or reversing dependencies is rejected.

The example exercises the complete machinery; its particular
formula also admits a much simpler proof from transitivity of the
stage. The two-clause example is a conditional extension test, not
an unconditional multi-clause reflection proof. All builders
remain fixed-formula, finite-arity code generators, not an
internally quantified truth theorem.

## Actual replay receipts

Seven parts:
- canonical: totality 23,393 nodes; strictness 12.
- omega: conditional omega range closure on the exact canonical
  319,831-byte step formula, 3,687 nodes.
- limit: successor-closed range limit 273 nodes; range implies
  reflecting-stage witness closure 41,801 nodes.
- base: four closed dependencies (136, 394, 27, 46 nodes).
- link: 96 nodes, eight exact implication applications.
- two_clause: five conditional/selector derivations (12,876,
  205, 566, 13,679, 12 nodes).
- recurrence: five generic conditional derivations (67, 3,104,
  3,326, 3,343, 3,687 nodes), using a small pure membership
  relation fixture; its totality is a hypothesis, not a claimed
  unconditional theorem for that relation.

All 20 proof trees across the parts passed, including the repeated
base proofs. Eleven recorded exact-interface checks and six negative
controls passed. Additional exact next-formula and conditional
consequent comparisons are performed without incrementing the
interface counter. The large monolithic composition hit an RPC
resource error, so the verification uses modular dependencies
instead; proof sizes are reported only when measured. The new
native Node CI matrix is pending. No paid compute was requested.

Replay:
  for part in canonical omega limit base link two_clause recurrence; do
    node research/ace/reflection_omega_replay.mjs "$part" > "/tmp/ace-n-$part.json"
    diff -u "research/ace/reflection_omega_${part}_receipt.json" "/tmp/ace-n-$part.json"
  done

## ACE-03O gate

Generalize the modular chain to several simultaneous witness clauses,
with actual discharged one-step bounds for each, and lift the current
clause-count and arity caps. Develop the fixed-formula finite-relation
program compiler/adequacy theorem for the pinned Def predicate, then
combine reflection with definability of the separated subset in a
successor stage. Check selected Separation instances before claiming
a complete schema generator. Replacement in L and Choice remain
open. Formal checker soundness, uniform textbook adequacy of the
definition, native Lean translation, and RH remain separate tasks.

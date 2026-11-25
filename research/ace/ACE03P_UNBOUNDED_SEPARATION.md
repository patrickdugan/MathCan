# ACE-03P | Two-clause reflection and modular unbounded Separation

Status: eight authoring-runtime replay parts passed for one fixed,
parameter-free, syntactically unbounded Separation predicate. The
proof chain is modular: the existing ZF checker checks each closed
dependency and the implication/cut links; the exact guarded target
is compared to the source axiom's relativization. A single expanded
certificate has not been submitted to the original compile()
certificates array. The pinned L AST and original kernel rules
are unchanged.

## Fixture

  phi(x) := (exists z, x in z) and (exists z, z in x).

The first quantifier has no bounding set in the input syntax. The
second existential is also written without a syntactic guard; its
membership condition implies a bound. This is a genuinely unbounded
syntactic fixture, but mathematically simple: in a class closed under
pairing, the first conjunct holds for every class member. It was chosen
to exercise simultaneous reflection rather than to demonstrate an
independent deep set-theoretic consequence.

## Simultaneous witness bounds and reflection

The fixed-formula transport generator extracts two witness clauses,
with bodies x in z and z in x. For each, ACE-03M constructs a
closed strict stage-extension proof via least demand ordinal,
functional Replacement, Union, and monotonicity.

The ACE-03N simultaneous selector theorem takes both strict
extensions as hypotheses. Their exact formulas are independently
built in the replay. Each antecedent is checked against its closed
proof, and a five-node implication application checks the total
canonical extension theorem's conclusion. Both premises are thereby
discharged in the modular chain.

The canonical step formula must match the independent reflection
linker's formula exactly. The omega recurrence theorem is instantiated
with this same two-clause formula. Its finite histories, uniqueness
of endpoints and Replacement range give a successor-closed ordinal
set. The limit theorem takes the union of that range and uses
limit-stage membership and monotonicity to place each finite
parameter tuple in an earlier member stage. The canonical successor
provides both witness clauses, which transfer to the limit. The
101-node reflection implication and 17-node application of its
eight antecedents check the final fixed-formula reflection conclusion.
Each premise has a separately checked proof or a checked link from
closed proofs.

## Shared limit dependencies

The initial two-clause limit replay exceeded the Code Mode timeout.
The optional shareImports mode in reflection_limit.mjs now binds
nine closed imported proofs once through ordinary implication
introduction/elimination (the existing proof builder's use helper).
This reduces repeated expansion of expensive stage-existence,
monotonicity and other derivations while retaining an ordinary
closed proof tree. The two-clause result checked with 18,522 nodes.
The previous ACE-03N default limit replay exactly reproduced its
original receipt (273 and 41,801 nodes, identical byte counts).

## Separation link

The new unbounded_separation.mjs builder takes six exact antecedents:
common constructible stage, stage monotonicity, stage transitivity,
definable-subset transport, fixed-formula reflection, and compiled
subset definability.

For a constructible separating set s (and the optional supported
single original parameter), choose a common stage and then a
strictly later reflecting stage A. Monotonicity puts s and the
parameters in A. Ambient Separation gives a set q defined by
membership in s and phi relativized to L. Transitivity places each
member of s in A. The reflection theorem transports truth of phi
between A and L. Thus q satisfies the compiler's exact subset slice
condition over A, with s inserted as a parameter. The compiler
provides D(A,q), and the successor-stage definability theorem
establishes L(q).

The 249-node Separation implication and its 13-node application
of six antecedents are checked. The exact pure conclusion equals
expandClass(rel(source Separation axiom), pinned L). Guard conversion
is checked from that pure formula; the original compiler translates
the source formula as an explicit hypothesis, and a final checked
cut discharges the corresponding target hypothesis. This certifies
the modular relativized axiom derivation, without claiming a direct
original compile() axiom-certificate-array import. No new trusted
inference rule or axiom policy is used.

## Measured verification

| Replay | Main checked proof nodes |
| --- | --- |
| left | 18,577 |
| right | 18,577 |
| selector | 13,679 conditional totality; 12 strictness; 5 application |
| omega | 3,687 |
| limit | 18,522 |
| base | 136; 394; 27; 117 |
| separation | 11,304; 3,750; 2,882; 5,053; 6,078 |
| links | 101; 17; 249; 13; 2; compiler 1/1; 5 |

Eight replay parts contain 17 closed proof-module checks and six
contextual link/translation checks (23 receipt entries), 35 exact
interface comparisons and ten negative controls. The counts include
repeated pinned-interface comparisons across independent replay
parts. All replay receipts are actual authoring-runtime results,
not projected counts. No paid compute used. New native Node CI
matrix registered; no claim of green CI until observed.

Replay:
  for part in left right selector omega limit base separation links; do
    node research/ace/unbounded_separation_replay.mjs "$part" > "/tmp/ace-p-$part.json"
    diff -u "research/ace/unbounded_separation_${part}_receipt.json" "/tmp/ace-p-$part.json"
  done

## ACE-03Q gate

Build a reusable modular certificate import interface that verifies
a topologically ordered closed proof graph and translates arbitrary
source derivations with certified axiom leaves by checked cuts, using
the original kernel without extra trusted rules. Generalize schema
instances to multiple parameters and lift the finite resource caps;
exercise deeper unbounded quantifier alternation. Then apply the
reflection and definability machinery to Replacement. The complete
unrestricted Separation schema, Replacement, Choice, uniform
definition adequacy, formal checker soundness and native Lean/RH
translation remain open. Seven fixed axiom families and four bounded
Separation instances have prior direct certificate imports; this
checkpoint adds one modular unbounded instance.

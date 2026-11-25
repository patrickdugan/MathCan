# ACE-03H | Coherence, restriction, uniqueness and monotonicity

Status: 13 closed object-language derivations accepted by the executable
ACE ZF checker. The two monotonicity premises are discharged by the
ACE-03F inflation proof. General stage-graph existence is still open.

## Coherence

Given transitive domains d,e and exact StageGraph(f,d), StageGraph(g,e),
bounded induction on d proves, at each index b in d, that if b belongs
to e, any values of f and g at b are equal. Transitivity of both domains
places every member of b in both domains. At a successor, Foundation
excludes a two-element membership cycle, which gives uniqueness of
the predecessor via the explicit successor membership characterization.
The induction hypothesis equates predecessor values, and Def uniqueness
equates successor values. Mixed successor/limit branches contradict
the limit branch's no-predecessor condition. In the limit/limit branch,
the membership equivalence for each union follows by transporting the
earlier witness values using induction. Extensionality equates the
limit values. Graph functionality identifies arbitrary values with
the witnesses chosen by the stage rules.

The proof does not use inflation or assert existence of arbitrary
stage histories.

## Restriction

For transitive e contained in d, use Separation on f with the condition
that an entry is a Kuratowski pair whose index lies in e. For each index
in e and each value, membership in this restricted graph is equivalent
to membership in f's graph. Totality and uniqueness transfer. For every
b in e, transitivity ensures that its predecessor indices remain in e.
Both successor and limit stage rules therefore transfer verbatim under
the value equivalence. This proves existence of a restricted stage
graph with all its values equal to the original graph on e.

## Graph uniqueness

Extensionality of singleton and unordered-pair components proves
uniqueness of Kuratowski pair objects with specified coordinates.
For two graphs on the same domain, pointwise equivalence of their
value predicates then implies equality of the graph sets. Combining
this with coherence proves that any two stage graphs on a common
transitive domain are equal. This is the uniqueness needed in a future
Replacement argument collecting compatible stage histories.

## Monotonicity

At b in a transitive graph domain, bounded induction proves that for
i in b, the value at i is a subset of the value at b. For a successor
b of j, the exact successor membership formula gives i in j or i=j.
Use induction or functionality to get inclusion in the stage at j,
then use inflation of Def on the transitive predecessor stage.
For limit b, membership in the earlier stage is directly sufficient
for membership in the union stage. The proof uses stage transitivity
and the already certified inflation theorem; the latter is discharged
by direct proof composition. Coherence transfers this conclusion to
two different histories at comparable indices, yielding closed
cross-graph monotonicity under the stated graph/domain hypotheses.

## Replay

stage_coherence.mjs rebuilds all 11 extended derivations, plus the
two unconditional monotonicity compositions (13 total). Three exact
conclusions are rebuilt independently in de Bruijn syntax. Five negative
controls reject inappropriate theory policies and mismatched inflation
premises. All checks passed in the authoring runtime.

Selected node counts: coherence 513; restriction 236; graph uniqueness
898; monotonicity 3031 after inflation; cross-graph monotonicity 3634.
Receipts report proof-tree nodes and compact serialized bytes, not
wall-clock performance or compressed proof sizes.

Run:
  node research/ace/stage_coherence.mjs > /tmp/ace-h.json
  diff -u research/ace/stage_coherence_receipt.json /tmp/ace-h.json

The default hierarchy builder output remains unchanged. No new
relativized axioms are claimed. The pinned constructible predicate
still needs uniform adequacy verification, and the executable object
proof checker still needs formal soundness verification. No paid
compute used.

## ACE-03I gate

Build one-step extensions, including a set of earlier values via
Replacement and the limit union. Establish an empty-domain stage graph.
Use uniqueness, restriction and compatible history unions to derive
general existence on ordinal domains by bounded induction. Then derive
pairing and union closure of L. Keep existence, definition adequacy,
and checker soundness as distinct obligations.

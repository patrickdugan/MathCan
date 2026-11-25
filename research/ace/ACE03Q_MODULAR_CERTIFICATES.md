# ACE-03Q | Checked modular axiom certificate imports

Status: reusable executable modular proof-graph verification and
source translation implemented. The synthetic and pinned-L bounded
Separation replays passed. A complete streamed unbounded Separation
graph runner is committed and registered for a longer Node CI replay;
its authoring-runtime execution timed out, so no completed end-to-end
receipt for that runner is claimed. The original object kernel,
relativization compiler and pinned L syntax are unchanged.

## Graph verification

A node has exactly {id, deps, goal, proof, guarded}. The declared
goal must be closed in the appropriate language. Every dependency
must name an earlier, successfully checked node, with no repeated
dependency identifiers or duplicate node identifiers. At each node
the existing kernel checks the proof with precisely the dependency
conclusions as its hypothesis context, at free-variable depth zero.
The computed conclusion must match the declared formula exactly.
The checker owns copies of accepted conclusions and snapshots the
class definition. Pure nodes cannot use a guarded formula as an
assumption. The entire graph shares a target theory chosen from
logic, CL and ZF and one class definition. ZFC target policy and
choice axiom imports are rejected.

The mathematical justification is induction on the topological
order and admissibility of cut for closed theorems. There is no
new axiom or inference rule added to the existing kernel. This
metatheoretic graph argument and the existing checker still need
formal soundness verification. A receipt alone cannot authorize
a theorem import: actual proof objects must be checked.

## Source translation

First check the original source derivation in its source theory.
For each certificate descriptor {spec,node}, compute the exact
source axiom formula under that policy and its relativization.
The graph node must conclude the exact relativized formula.
Duplicate certificates are rejected.

Replace axiom leaves in the source proof with ordinary hypothesis
references to the corresponding closed source axiom formulas,
appended after the external context. Shift all existing local
hypothesis indices by the number of certificate hypotheses, leaving
external hypothesis indices unchanged. The rewrite traverses only
the proof positions of the rules, not formula ASTs. Recheck the
rewritten proof with the augmented source context. The existing
compiler translates this proof using zero original tree-certificate
imports. Check the exact target formula and target context.

Discharge the additional target assumptions with an ordinary
implication-introduction wrapper. The original kernel checks the
result under only the external translated context. Finally verify
the implication-elimination chain with the closed certificate
conclusions and the conditional target theorem as assumptions.
By the modular cut argument, the final sequent needs only the
external target assumptions. This also handles source proofs
under free-variable guards, existential elimination and local
hypotheses introduced under quantifiers. The result includes the
checked conditional and cut, not a claim that a monolithic
closed tree was emitted.

## Actual replay results

Synthetic fixture: the empty-object class from ACE-03C. Eleven
graph nodes verify four certificates (extensionality, empty,
union and foundation). Eleven source proofs cover repeated
axiom leaves, local hypothesis indices, open contexts, universal
and existential rules, disjunction elimination, equality
substitution and classical reasoning.

| Source fixture | Original target nodes | Modular translation nodes |
| --- | --- | --- |
| conjunction | 106 | 3 |
| duplicate leaf | 43 | 3 |
| open axiom | 46 | 3 |
| local under binders | 28 | 8 |
| existential branch | 113 | 10 |
| disjunction branch | 50 | 10 |
| equality substitution | 25 | 5 |
| classical | 25 | 5 |
| universal elimination | 87 | 4 |
| existential introduction | 26 | 6 |
| no axiom | 3 | 3 |

The graph itself has 185 checked proof visits. The modular target
column excludes graph validation, the conditional wrapper and
cut verification. Twenty-four exact comparisons and 21 negative
controls passed, including forward/self dependencies, duplicate
nodes, wrong class, forbidden theory/choice, open node goals,
bad certificate matching, and a nested closed import attempting
to use an external hypothesis. The mutation regression checks
that verified conclusions are independently stored.

Pinned-L bounded Separation: use the prior exact proof for
phi(x,p) := x in p, with a pure closed node and a guard conversion
node. Translate a seven-node source derivation using the same
axiom twice, including under a universal binder. Original
tree compiler target: 40,330 nodes. Modular graph: 20,161 visits
once (20,159 pure proof + 2 conversion); rewritten source 7,
translated target 8, checked implication wrapper 9, final
cut 3. The target conclusion and external context match the
original compiler exactly. Two negative controls passed. Total
across the completed replays: 26 exact comparisons and 23
negative controls.

The unbounded replay constructs a topological DAG from the
ACE-03P two-clause reflection proof, including both strict
extensions, selector, omega recurrence, shared limit,
transport, reflection link, finite subset definability,
Separation link and final guarded axiom. It invokes the new
importer on a repeated source axiom under a quantifier.
The full authoring runtime timed out; earlier ACE-03P component
checks remain verified. The CI job checks the exact final
target and uploads an actual receipt if it completes. It is
not diffed against a predicted receipt.

## Replay

  for part in synthetic bounded; do
    node research/ace/modular_certificate_replay.mjs "$part" > "/tmp/ace-q-$part.json"
    diff -u "research/ace/modular_certificate_${part}_receipt.json" "/tmp/ace-q-$part.json"
  done

  node --max-old-space-size=6144 research/ace/modular_unbounded_replay.mjs

No paid authoring compute used. The PR import-list conflict with
main was isolated by moving the same three ACE imports to a
separate insertion point (no import added or removed on the
research branch); native Lean/Node CI remains to be checked.

## ACE-03R gate

Complete the streamed unbounded graph replay and pin its actual
receipt. Generalize Separation assembly to multiple original
parameters, then use the reflection and rank-bound infrastructure
to prove Replacement instances. Keep unrestricted schema
coverage, constructible well-order/Choice, uniform textbook
adequacy, formal checker soundness, native Lean translation
and RH as separate obligations.

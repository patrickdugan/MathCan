# ACE-03S | Unbounded Replacement via two-parameter reflection

Status: seven split replays for a fixed unbounded Replacement instance
passed the executable ZF checker. Every dependency formula matches the
generated graph interface, and every cut and the exact source translation
has been checked. The full streamed graph import was attempted but
exceeded the authoring runtime's execution limit. No completed full-run
receipt is claimed. The pinned unary L formula and original kernel rules
are unchanged.

## Relation and reflection fixture

The source relation is

  phi(y,x) := forall z, x in z -> y in z.

It is syntactically unbounded: there is no set restricting z in the
source quantifier. In a class closed under singleton formation this
particular relation is equivalent to equality. The fixture tests
universal counterexample transport, two free-variable indices and
image definability, not a new deep consequence of set theory.

The reflection generator extracts one counterexample clause with
two parameters y,x and body not (x in z -> y in z). The checked
strict witness-extension theorem gives a larger stage containing
a counterexample whenever one exists in L for any pair of
parameters in the old stage. Its proof uses the existing least
demand ordinal and functional Replacement aggregation machinery.

The exact counterexample extension is reconstructed independently
in de Bruijn syntax. The canonical selector's conditional
totality conclusion and its strictness theorem are checked against
the independent reflection linker's formulas. A three-node cut
applies the closed extension to obtain totality. The omega recurrence
is checked on the exact canonical step formula. The shared-import
limit theorem places each finite parameter tuple in a member
stage, applies the successor witness property and transfers the
counterexample into the limit stage.

The checked Tarski-Vaught transport implication now has a universal
counterexample clause. The 96-node reflection implication and
17-node logical application yield the reflecting-stage conclusion
for phi, with both free parameters in scope.

## Replacement link

The bounded Replacement construction in ACE-03R has an optional
reflected mode. Ambient Replacement still collects all outputs of
the L-relativized functional relation into a set b. Adjoin the
domain a and all parameters to b and apply the constructible-rank
bound, obtaining an exact stage value r containing them. Stage
reflection supplies a strictly larger ordinal and a stage value s
on which phi agrees with its L-relativization. Cross-history
monotonicity transports the entire original bound into s.

Transitivity of s puts each element of a in s. The image membership
condition is therefore precisely the slice

  y in b iff y in s and exists x in s,
                         x in a and phi restricted to s.

The finite-program compiler supplies D(s,b) for this image formula.
The successor-stage definability theorem proves L(b). The exact
relativized image condition follows from the ambient image
specification. All steps are derived from the source functionality
antecedent; no unconditional functionality claim is imported.

The reflected link has eight closed dependencies: L transitivity,
the constructible-set rank bound, stage transitivity, stage
membership implies L, definable-subset transport, fixed-formula
reflection, finite image definability and stage monotonicity.
The 614-node implication is checked. Its 17-node cut yields the
pure conclusion, which is independently compared to the expansion
of the exact guarded source Replacement axiom. Guard conversion
uses the original kernel and pinned L.

The original bounded mode is preserved. The previous identity
Replacement replay reproduced its full receipt exactly.

## Actual split replays

| Part | Checked proof nodes |
| --- | --- |
| extension | 20,133 |
| selector | 4,815 conditional; 12 strictness; 3 cut |
| omega | 3,687 |
| limit | 18,476 |
| base | 136; 394; 27; 122 |
| replacement | 2,897; 8,882; 2,882; 5,053; 3,750; 9,586 |
| links | 96; 17; 614; 17; 2 |

The seven receipts contain 21 checked graph-node proofs (17
closed modules and four contextual applications/conversion),
81,601 kernel visits, and seven rejection controls. Additional
exact comparisons check the extracted clause, canonical step,
shared stage interface and independent source-schema expansion.
No receipt is used as a substitute for a proof object.

The source derivation uses the same Replacement axiom twice,
including universal introduction/elimination, and has five
nodes. The source hypothesis rewrite, ordinary compiler target
(8 nodes), conditional wrapper (9 nodes) and final cut (3 nodes)
are checked in the links replay. The resulting guarded target
is the conjunction of the exact axiom formula with itself.
The modular proof chain discharges the contextual assumptions
by the separately checked closed dependencies.

The full runner feeds these same 21 nodes in topological order
into compileModular. Its single authoring-runtime execution
timed out. A separate CI job checks the complete graph and
uploads an actual receipt only if the run completes successfully.
The split CI matrix diffs against the measured receipts.

Replay:

  for part in extension selector omega limit base replacement links; do
    node research/ace/unbounded_replacement_replay.mjs "$part" > "/tmp/ace-s-$part.json"
    diff -u "research/ace/unbounded_replacement_${part}_receipt.json" "/tmp/ace-s-$part.json"
  done
  node --max-old-space-size=6144 research/ace/unbounded_replacement_replay.mjs full

The full streamed unbounded Separation replay from ACE-03Q remains
unverified at the time of this checkpoint. Its ACE workflow
45596235187 was queued; the previous MathCan mathematical checks
workflow 45596234798 completed successfully. The ACE-03R
workflows were still queued when checked. No paid authoring
compute was used.

## ACE-03T gate

Develop the canonical well-order construction for constructible
stages, beginning with a fixed well-order of finite relation
programs and lexicographic finite parameter tuples over a
well-ordered stage. A definable subset may have many defining
codes; choose its least code in that well-order and prove the
induced ordering is a well-order. At successor stages this
provides the local mechanism needed for Choice. Coherent
transfinite construction and definability of the canonical
well-order in L remain necessary. The complete Separation and
Replacement schemas, finite resource caps, formal checker
soundness, uniform textbook adequacy and native Lean/RH
translation remain separate open obligations.

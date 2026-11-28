# ACE-03R | Bounded Replacement via functional images and rank bounds

Status: four complete modular imports of exact fixed Replacement instances
passed the executable ZF checker. The original kernel and the pinned unary
L formula remain unchanged. The unrestricted Replacement schema remains
open, as do formal checker soundness and uniform definition adequacy.

## Functional image in the ambient universe

Fix a pure set-language relation phi(y,x,ps), with output y, input x
and parameters ps. Assume L(a), all parameters belong to L, and the
exact relativized source Replacement antecedent: for every x in L
and a, there is a unique y in L satisfying phi restricted to L.

Transitivity of L puts every member of a in L. Ambient Replacement
is instantiated with the formula L(y) and phi restricted to L.
Its totality and uniqueness antecedent follows from the given
relativized antecedent. Thus there is an ambient set b whose members
are precisely the outputs for x in a satisfying that guarded relation.
Each member of b belongs to L, including when the original domain
is empty (the property is then vacuous).

Adjoin a and every parameter to b using ordinary Pairing and Union.
All elements of the resulting bounding set S belong to L. Apply
ACE-03L's functional least-rank bound to find an ordinal c and exact
stage value r such that S is a subset of r. This contains all image
members, a, and the parameters. Stage transitivity puts every
member of a in r. The stage inclusion theorem puts every member of r
in L.

## Definability of the image

Use the ACE-03O bounded-absoluteness generator on phi(y,x,ps).
For y and x in r and parameters in r, truth restricted to r equals
truth restricted to L. The exact image characterization gives

  y in b iff y in r and exists x in r,
                         x in a and phi restricted to r.

Forward: y is in r by the bound, and the ambient image witness
x is in a, hence in r by transitivity. Backward: y in r gives L(y);
local truth transports to L, and the ambient image specification
yields y in b.

Compile the image formula exists x (x in a and phi(y,x,ps)) using
the finite relation program compiler. The source relation's free
indices are [y,x,p0,...]; the image formula's free indices are
[y,a,p0,...]. The existential binder for x is inserted with a
capture-safe remapping of all free indices. The compiler proves
D(r,b) from the exact slice condition. The successor-stage
definability theorem yields L(b). Its ambient image membership
condition immediately implies the exact relativized Replacement
conclusion, using transitivity again for the guarded input witness.

The Replacement link is a pure proof with seven explicit closed
antecedents: L transitivity, constructible-set stage bounding,
stage transitivity, stage membership implies L, definable-subset
transport, bounded absoluteness of phi, and image definability.
All seven are independently regenerated and checked, not supplied
as unproved assumptions. A checked implication-elimination chain
derives the pure closed conclusion. Independently expand the exact
relativized source schema and compare it to that conclusion. A
guard-conversion node gives the exact guarded certificate.

## Actual imports

Each ten-node dependency graph is verified by ACE-03Q's modular
importer. The source derivation contains the same Replacement
axiom twice, once under universal introduction and elimination.
The original source derivation (5 nodes), rewritten source,
translated target (8 nodes), conditional wrapper (9 nodes),
and final cut (3 nodes) are checked. Both target conjuncts match
the exact guarded axiom, with no external assumptions.

| Fixture | Parameters | Image-definability nodes | Link nodes | Graph kernel visits |
| --- | --- | --- | --- | --- |
| identity: y=x | 0 | 4,404 | 474 | 24,648 |
| singleton: x in y and forall z in y, z=x | 0 | 11,397 | 474 | 31,714 |
| constant: y=p | 1 | 5,147 | 685 | 25,604 |
| conditional: (x in p and y=q) or (x notin p and y=x) | 2 | 17,460 | 926 | 38,296 |

The certificates prove schema instances, i.e. the implication
from functionality and totality. They do not independently prove
the functionality antecedent for every possible relation.

Across four parts: 40 checked graph nodes (10 per graph), 120,262
graph kernel visits, 44 exact comparisons and 16 negative controls.
The controls reject inappropriate logic policy, a missing link
dependency, the wrong class definition, and an uncertified source
axiom. The reported graph counts include repeated shared lemmas
across separate replay runs; they are not a deduplicated combined
proof size or wall-clock benchmark.

The two-parameter instance initially exceeded the finite compiler's
16-instruction cap. Raise it to 20, retaining the three-parameter
and six-coordinate limits (the separating or image-domain set
uses one parameter). The full two-parameter conditional fixture
then passed. The previous ACE-03O four-formula compiler receipt
reproduced exactly after the cap change.

## Replay

  for part in identity singleton constant conditional; do
    node research/ace/replacement_replay.mjs "$part" > "/tmp/ace-r-$part.json"
    diff -u "research/ace/replacement_${part}_receipt.json" "/tmp/ace-r-$part.json"
  done

All four receipts are actual authoring-runtime results. Node CI
has a four-part replay matrix. The prior ACE-03Q full streamed
unbounded Separation CI job is still queued at the time of
checking (workflow 45596235187); no completed full-graph receipt
is claimed. No paid authoring compute.

## ACE-03S gate

Replace bounded absoluteness in the image link by a formula-indexed
reflecting-stage interface. Begin with the rank-bound stage
containing all image elements, the domain and parameters, then
enlarge to a reflecting stage for the relation phi. Monotonicity
preserves all memberships used in the image slice. Reuse the
finite-program compiler and modular graph importer for an actual
unbounded Replacement instance. Generalize formula and parameter
caps and prove unrestricted schema coverage separately. Choice
via a canonical constructible well-order, formal checker
soundness, uniform textbook adequacy, native Lean translation
and RH remain outstanding.

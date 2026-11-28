# ACE-03I | General ordinal stage recursion

Status: 19 closed object-language derivation trees accepted by the
executable ACE ZF checker. Eight independently reconstructed exact
conclusions and six rejection controls passed. General existence and
uniqueness of histories on ordinal domains, and existence and uniqueness
of their ordinal stage values, are checked for the pinned formulas.

The checker itself has not been formally verified. Uniform adequacy of
the candidate constructible predicate relative to textbook L remains a
separate obligation; this checkpoint does not prove that L satisfies all
ZFC axioms.

## Next-stage values

For a function graph f on b, classical excluded middle distinguishes
whether there exists a predecessor i in b with Succ(i,b). In the
successor case graph totality supplies the preceding value and the
ACE-03E Def existence theorem supplies the next value. In the limit
case, Replacement with body Val(f,i,y) collects the range of f on b.
The graph's existing totality and uniqueness discharge the Replacement
antecedent. Union of this range gives the exact limit-stage formula.
Neither case uses choice.

## One-stage extension and compatible unions

Successor existence is proved by adjoining b to itself via Pairing,
singleton formation and Union. A similar construction adjoins the
Kuratowski pair (b,r) to a stage graph f on transitive b, where r is
the next-stage value. Foundation excludes b in b. The proved ordered
pair injectivity and value-domain lemma ensure that the new entry
does not change any old graph value. The stage-rule transport lemma
proves old stage rules remain valid under this extension and that the
new index has the required stage value. This establishes extension
from b to any specified successor d.

For a set H of histories whose transitive domains are subsets of d,
assume their domains cover d. Union(H) is a graph on d: each entry
comes from some member history, totality comes from coverage, and
functionality follows from ACE-03H coherence. On the domain of each
member history its values are equivalent to that history's values.
The stage-rule transport lemma therefore verifies the successor and
limit rules in the union. This construction does not require
choosing one history per index using AC.

## Transfinite induction and Replacement

Write Hist(i,h) for the exact formula
  exists e, Succ(i,e) and StageGraph(h,e).
For transitive i, uniqueness follows from uniqueness of successors,
transitivity of the successor domain and uniqueness of stage graphs.

Use the bounded induction instance with property
  Ord(i) -> exists h, Hist(i,h).
For ordinal b, all earlier indices i in b are ordinals. The induction
hypothesis and Hist uniqueness give exactly the Replacement antecedent
for Hist(i,h). Replacement collects all earlier successor histories
into H. Each such history has a transitive domain contained in b,
and the domains cover b since i belongs to its own successor.
The compatible-history union theorem gives a history on b; extend it
one stage to get Hist(b,h). Apply bounded induction on the successor
of b, which is transitive and contains b. This proves the property
for every ordinal b.

Restriction produces a stage graph on b itself. The previous
same-domain uniqueness result proves
  forall b, Ord(b) -> exists unique f, StageGraph(f,b).
The separate successor-history theorem supplies a unique value at
index b for each ordinal b. Every member of that value satisfies the
pinned L predicate by introducing the very same graph witnesses.

## Verification and size

stage_recursion.mjs emits all 19 proof trees. Prior closed proofs
are imported by shifting their local hypothesis indices by the
current context length; each resulting tree is checked from empty
hypotheses, free-variable depth zero, pure language mode and ZF policy.
The generated L AST is compared against L_formula.json before checking.
Eight final goals are reconstructed independently from the pinned
formulas using de Bruijn indices. Six negative controls reject
incorrect theory policies or proof applications.

Selected sizes:
- Stage history extension: 1,241 nodes.
- Compatible-history union: 1,216 nodes.
- Successor-history existence: 3,940 nodes.
- Ordinal-history existence: 4,213 nodes.
- Ordinal-history existence and uniqueness: 5,138 nodes, 7,606,763
  compact JSON bytes.
- Ordinal stage value existence: 3,976 nodes.
- Ordinal stage value uniqueness: 623 nodes.
- Stage membership implies L: 27 nodes.

Proof tree sizes include repeated syntax and are not measurements
of runtime or compressed certificates. All new proof objects were
replayed in the authoring JavaScript runtime; new Node CI remains
pending. No paid compute.

Replay:
  node research/ace/stage_recursion.mjs > /tmp/ace-i.json
  diff -u research/ace/stage_recursion_receipt.json /tmp/ace-i.json

## ACE-03J gate

Prove ordinal comparability and obtain a common stage containing any
two L elements. Construct explicit finite-program witnesses for pair
and union definability over a transitive stage, and use the stage
existence and coherence theorems to place the results in a successor
stage. Then discharge the previously checked generic pairing and union
closure certificates. Infinity, power set, separation, replacement,
choice, full definition adequacy, checker soundness and RH translation
remain separate outstanding tasks.

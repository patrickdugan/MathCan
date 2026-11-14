# SWC-01: finite graph-witness formalization

Date: 2026-11-14. Companion to Control-Harness's
Symmetry Witness Control campaign and the OpenAI
mathematics families #133 and #243.

The scope of this MathCan Lean 4 / Init module is
**finite arithmetic and graph enumeration**.
The graphs share a 16-vertex Z4×Z4 vertex set:

- Rook graph: connect vertices in a common row or column.
- Shrikhande graph: connect coordinate differences
  ±(1,0), ±(0,1), ±(1,1) modulo four.

## Kernel-checked facts

[MathCan/GraphWitness.lean](../../MathCan/GraphWitness.lean)
defines both relations explicitly. For every
vertex, it checks six neighbors. For every pair
of distinct vertices, it checks exactly two
common neighbors, establishing the (16,6,2,2)
finite strongly regular parameters.

For every anchor, the induced neighborhood
contains exactly two triangles in the rook
graph and none in Shrikhande. Each such
triangle, together with the anchor, is a
four-clique. The module verifies an explicit
rook clique and the total anchored counts
32 and zero.

The finite incidence identities imply eight
four-cliques in the rook graph, since each
four-clique is counted at its four vertices.
There are none in Shrikhande.

All statements are compiled by MathCan.lean,
and their transitive axioms are printed
within the standard mathcan-proof-audit workflow.
The supplementary swc01-graph-witness workflow
directly compiles the same source.

## Scope boundaries

The general 2-WL indistinguishability proof
uses the strongly regular parameters and the
inductive pair-color update rule, and is
written in Control-Harness's THEORY.md.
The finite Python reference executes the
joint WL2 and WL3 algorithms directly.
The Lean file does not define the general
WL refinement semantics.

The proof that eight edge deletions are
necessary to eliminate all rook four-cliques
uses the edge-disjoint row and column
witnesses. The executable reference checks
the disjointness and constructs a matching
eight-edge attack. The Lean module only
formalizes the underlying graph and
local witness counts.

The source OpenAI #133 high-dimensional
WL complexity lower bounds and #243
choiceless counting/witnessed-choice
expressive separations are external
research claims. This module does not
reproduce either general theorem.
An external random anchor is a simple
finite symmetry-breaking interface,
distinct from the particular witnessed
symmetric-choice logical operator of #243.

No trained neural model or production
graph-control system has been evaluated
by these exact finite proof checks.

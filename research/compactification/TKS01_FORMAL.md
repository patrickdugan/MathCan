# TKS-01: finite thin spanning tree and k-server kernel bridge

Date: 2026-11-14. Companion to the Control-Harness TKS-01 campaign, drawing
OpenAI Mathematics #110 (randomized k-server) and #174 (strong thin spanning
trees) into a controlled test of graph-service metric fidelity.

## Formalized finite mathematics

MathCan/ThinServer.lean uses the repository pinned Lean 4/Init kernel.
It defines K8 unit-cut capacity for every one of 256 vertex masks and
the unit spanning-path cut crossing count. For all 254 nontrivial masks,
the kernel verifies

    112 * path_cut(mask) <= 49 * complete_cut(mask),

equivalent to |delta_T(S)| <= (49/16)/7 * |delta_K8(S)|.
The alternating vertex cut mask 85 attains equality at
tree capacity seven and original capacity sixteen.
The normalized thinness constant is therefore exactly 49/16.

It also checks the sum of all 28 distinct unordered pair distances on
the path is 84, giving average tree distance three, while the original
complete-graph pair distance is one. For two servers at vertices
zero and one, a request for vertex seven requires six tree movement
units and only one original graph movement unit.

The finite failover lemma verifies removing path edge (3,4) disconnects
the tree across the first-four/last-four cut, while deleting that one
edge from the original K8 leaves fifteen crossing edges.

A general arithmetic lemma composes three source-independent
inequalities, cost_G <= cost_T, cost_T <= c*OPT_T+a, and
OPT_T <= sigma*OPT_G, to conclude

    cost_G <= c*sigma*OPT_G+a.

Its interpretation for expected randomized k-server movement under
source #110 policy model is a separate mathematical argument in
Control-Harness THEORY.md. This Lean proof itself concerns natural
numbers and a supplied system of cost inequalities.

## Mathematical scope

The general formula C_n=(n-1)^2/floor(n²/4)<4, the expected path
stretch (n+1)/3, and the exact k-server offline cost mismatch
are proved in the Control-Harness mathematical note and tested by
complete finite cut and server-action enumeration. The Lean module
formally verifies the K8 test instance, not the full all-n proof.

Source #110 randomized k-server construction and #174 general
strong-thin-tree algorithm are not formalized or executed here. The
TKS-01 tree is constructed explicitly as a path. No live route
provider, neural checkpoint, agent interaction or production system
is assessed in this finite bridge.

## CI

MathCan.lean imports the module. The original mathcan-proof-audit.yml
compiles it and prints its transitive axioms, rejecting admitted or
reduction-shortcut axioms. The existing MathCan Python and Lean
regression suites run unchanged. A dedicated TKS-01 kernel workflow
also checks the added file directly and uploads its axiom output.

All new TKS-01 work stays in a draft branch for review. The earlier
open SCT MathCan PR #39 has separate proof ownership.

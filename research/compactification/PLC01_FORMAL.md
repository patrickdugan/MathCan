# PLC-01: Exact five-vertex SDP and L1 cut certificates

Date: November 14, 2026.
Companion to Control-Harness PLC-01, combining OpenAI Math #089
(planar/bounded-treewidth L1 embedding) and #117 (uniform sparsest
cut Goemans–Linial SDP gaps).

## Kernel-scoped results

MathCan/PlanarCutGap.lean defines the unit-capacity K2,3 supply
graph on five labeled vertices, with unit all-pair demand.
Lean checks all thirty nontrivial vertex cuts and proves
the integer inequality demand_cut <= 2*supply_cut,
with a singleton B cut attaining ratio 1/2.

It defines the candidate GL metric with squared distances
d01=4/3, within the other three-vertex group distance 2,
and cross-group distance 1. Distances are stored with an
integer scale factor of three. Lean verifies all 60 ordered
triangle inequalities, computes the exact integer Gram
entries scaled by three, and checks every pair's distance
matches the squared Gram-distance formula. It also
checks the candidate SDP supply and all-pair totals,
18/3 and 40/3, certifying ratio 9/20.

The zero-sum integer negative-type test vector
(3,3,-2,-2,-2) gives zero for the GL metric and
a positive value 6 for the original K2,3 shortest-path
metric. The module checks the scaled versions.
The latter graph shortest-path metric therefore
cannot be substituted as a feasible GL metric.

For the integer hypermetric weights (-1,-1,1,1,1),
all possible cut metrics satisfy the nonpositive
weighted-pair inequality. The explicit SDP metric
violates that inequality. A nine-cut nonnegative
metric combination uses six 2/9-weight A/B doubletons
and three 5/9-weight B singletons. Lean checks its
distance bounds after clearing denominators,
including the 11/9 upper stretch, and verifies
every cut in the support has exact integral
sparsity 1/2.

The source PLC-01 mathematical note separately proves
the candidate Gram matrix is PSD via a sum-of-squares
formula and that its SDP value is globally optimal
under symmetrization. The Lean file checks the
finite Gram identities and SDP objective rather
than a generic theorem about all PSD matrices.

## New independent mathematical scope beyond this Lean file

The companion theorem proves a sharp L1 distortion
formula for the shortest-path metric of every planar
K2,m graph, m>=2. Explicit cut decompositions and
integer hypermetric duals match, with distortion
approaching 3/2. The verifier checks all pair
values through m=10. The all-m proof is a
handwritten even/odd combinatorial argument,
not a kernel-checked theorem in this module.

Combined conditionally, source #117 high integrality-gap
SDP metric families and source #089 finite planar
L1 constants imply an asymptotic obstruction
to constant-distortion approximation of those
optimal SDP metrics by planar shortest-path
metrics. Neither general source theorem is
reproduced by the local finite proof.

## CI

MathCan.lean imports PlanarCutGap, and the
standard mathcan-proof-audit workflow prints
transitive axioms and rejects sorryAx or
ofReduceBool. The dedicated PLC-01 workflow
also compiles the module directly in pinned
Lean 4. Original MathCan regressions remain
unchanged, with 583 Python tests in the
base suite.

There is no trained neural controller,
production authorization system or
Bitcoin consensus model in this finite
proof exercise. The associated Control-Harness
gate checks a declared numeric threshold
on cut sparsity and rejects relaxation-only
proofs lacking an actual cut partition.

The PR remains an unmerged review draft.

# RH-26E-04A registration: overlap-corrected finite rank capacity

**Date:** 2026-11-24 (Asia/Manila). Frozen before executable proof or CI.
**Host:** MathCan draft PR #265, branch research/rh26-extraction-rubrics-20261123.
**Source inspiration:** frozen leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b, GoodPointMultiplicityLeRankProof.lean:50–149, as inspected in RH26B08_RANK_CERTIFICATE.md. No new upstream source read or imported upstream proof.

## Question

Can we independently certify the local capacity mechanism, and exactly separate duplicate row-label counts from linear dependence of distinct row subspaces? The original MultLe theorem uses disjoint label sets, indexed independent subspaces, local multiplicity bounds and a theta injection. This experiment proves a general finite algebraic abstraction and explicit counterexamples. It does not establish the analytic hypotheses, actual automorphic spaces, or any global growth exponent.

## Mathematical contracts

Use finite label and index sets, natural weights d(s) and counts m(i). For finite selected sets A(i), write U for their union, r(s) for the number of selected sets containing s, D for the weighted duplicate defect sum over U of (r(s)-1)*d(s), and T for the double sum. All counts are natural; no assumptions on signs of real weights are implicit. For subspaces use a field K and finite-dimensional V. Require true indexed independence, not just pairwise intersection-zero.

Freeze the following ten public declaration names in namespace RH26E04A:

1. occurrence_positive: s belongs to U iff its occurrence count r(s) is positive.
2. weighted_count: T = sum over U of r(s)*d(s).
3. overlap_identity: T = sum over U of d(s) + D, including empty index/label sets.
4. overlap_zero_of_disjoint: if A(i) pairwise disjoint on the selected indices, D=0.
5. budget_with_overlap: local m(i) <= sum_{s in A(i)} d(s), and union weight <= R, imply total m <= R+D.
6. independent_union_rank: for a finite family of indexed independent subspaces, the sum of their dimensions on a finite label subset is the dimension of their span, hence bounded by dim V. Use an independently authored proof or a Mathlib theorem; do not copy upstream proof text.
7. subspace_capacity: instantiate budget_with_overlap at row dimensions and R=dim V using independent_union_rank. In particular exact disjointness removes D.
8. rank_nullity_defect: arbitrary linear F:W→V between finite-dimensional spaces satisfies dim W=dim range F+dim ker F. The kernel dimension bounds overcount when a certified combined map is supplied; the theorem makes no assumption that an arbitrary W is a particular direct sum.
9. duplicate_label_fixture: two sets {0,1},{1,2} in Fin 3, unit weights, total 4, union weight 3, duplicate defect 1; explicit failure of the uncorrected bound, while corrected bound is tight.
10. dependent_lines_control: in a two-dimensional rational vector space, three nonzero vectors e1,e2,e1+e2 have pairwise independent directions (pairwise linear independence or explicit pairwise trivial line intersections), but their triple is linearly dependent. Require an actual linear dependence or a proof that the associated map has a nonzero kernel, and each pair independent by direct calculation.

## Acceptance and compute

Ten declarations compile on pinned Lean 4.35.0 / Mathlib v4.35.0, all ten exact axiom reports, only propext, Classical.choice, Quot.sound permitted. No admissions or custom axioms. Controls must be positively proved counterexamples. No weakening contracts after the first run. Use isolated research/rh26/lean/RH26E04AOverlapCapacity.lean and existing experiments/deligne_mathlib environment; one GitHub-hosted CPU job per code/workflow change, 25-minute timeout. Record compiler/Mathlib pins, source SHA-256, elapsed time/RSS, literal audit artifact and any failed receipts. Pending verification is not PASS. No full Deligne build, upstream build, GPU/QPU or paid cloud.

After closure consider E04B block-scalar injection stability and E04C weighted capacity dual. B09 remains a separate bounded source-inventory session. Update CHUNK_INVENTORY.md, LEDGER.md and PR #265.

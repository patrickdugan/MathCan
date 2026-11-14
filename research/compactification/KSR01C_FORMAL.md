# KSR-01C: coarse-state dependence, finite kernel bridge

Date: 2026-11-14. Companion to Compactification Theory PR #124 and its research/tree_reconstruction_locality_v1/THEORY_C.md.

MathCan/CoarseStateDependence.lean is compiled through MathCan.lean and included in the original transitive-axiom audit. The verified workflow at commit a12dfd3066de5118ad9afdb193c062436d7fb7bd is https://github.com/patrickdugan/MathCan/actions/runs/43551696322.

## Formalized statements

For arbitrary integers a,b, the kernel checks

    2*(a*a+b*b) - (a+b)*(a+b) = (a-b)*(a-b).

After division by a common positive denominator, this is the two-parent conditional covariance numerator used in KSR-7. The file also checks the finite Boolean example in which two children copy a shared hidden parent: the joint zero-label mass is 1/2 and the product of the marginals is 1/4, encoded by exact counts.

For the fully shared critical branching example b=4, lambda=1/2, the normalized moment recurrence V_0=1, V_(L+1)=V_L+3 has exact solution V_L=1+3L. The kernel verifies that recurrence and the numerical cross-multiplied inequalities 5/7>2/3 and 1/2<=2/3, corresponding to the invalid independent-child guarantee and the valid corrected guarantee in the finite example.

## Scope

The formal file proves finite algebra and count identities. It does not formalize conditional expectation, the arbitrary-prior posterior covariance inequality, or minimal state-refinement optimality. Those probability statements have handwritten proofs and exact finite Python tests in Compactification Theory. The frozen native GRU audit is an executed model experiment with exact probabilities conditional on floating-point replay, not a Lean neural-network verification.

The original KSR source #229/#236 infinite-tree claims and the pre-existing TreeReconstruction.lean arithmetic are unchanged. Both Lean kernel/axiom checks and the existing rational-oracle workflow passed in the cited run. The PR remains a draft and is unmerged.

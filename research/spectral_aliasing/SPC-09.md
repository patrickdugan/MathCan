# SPC-09: causal compression bounds and finite witnesses

## Mathematical bounds (paper proofs, not Lean certificates)

1. Let J0:V->Y, B:V->Z and K=ker J0. The deferred quotient is
K/(K intersect ker B). Rank-nullity for B restricted to K gives dimension
rank(B|K)=rank([J0;B])-rank(J0), at most min(dim V-rank J0, dim Z).
Projection from im([J0;B]) onto im J0 has kernel {0}xB(K), proving the identity.
This is local linear algebra at one state, not nonlinear identifiability.

2. For x[t+1]=F[t](x[t]) and compressed z[t+1]=Q[t+1]F[t](z[t]), let
e[t]=||x[t]-z[t]||, q[t]=||Q[t]|| and assume F[t] is L[t]-Lipschitz on
a set containing both trajectories. Then
e[t+1] <= ||(I-Q[t+1])x[t+1]|| + q[t+1] L[t] e[t].
Add/subtract Q[t+1]F[t](x[t]) and use the triangle inequality. Iteration
gives e[T] <= e[0] product(q L) + sum of each omitted energy square root
times the subsequent product(q L). Orthogonal projections have q<=1;
oblique retention requires its measured operator norm. Affine centering
uses ||(I-Q)(x-mean)|| in the omitted term.

3. For observation Jacobians O and O+E, G=O*O obeys
||G'-G|| <= 2||O||||E||+||E||^2 by expansion O*E+E*O+E*E.
For deferred O N and perturbed O' N',
||O'N'-ON|| <= ||O'-O||+||O|| ||N'-N|| for orthogonal N'.
An eigenspace stability claim additionally requires an eigenvalue gap;
near-zero singular values can make numerical nullspaces unstable.

4. If a reference phase has distance gap g>0 to every competing phase,
a state perturbation of norm <g/2 preserves its nearest-reference label:
the true distance is <g/2 and all competing distances >g/2. After T updates,
a sufficient condition is product(L[t])||delta||<g/2. This proves phase
registration only, not correct algorithmic output. At equality ties can occur.

5. If C is M-Lipschitz on the trajectory tube, output error <=M e[T].
The bound in (2) therefore controls future output error using square roots
of omitted energies. For one-shot differentiable perturbations with
Hessian norm <=H on the perturbation segment,
||O(h+delta)-O(h)-DO(h)delta|| <= H||delta||^2/2, by integrating the
Jacobian along that segment. Local Jacobian norms at sample points alone
do not certify tube-wide L, M or H. Empirical measured norms are diagnostics,
and no global bound is asserted for the trained transformer.

New finite Lean witnesses and exact arithmetic tests live in MathCan. They
are explicitly separate from these analytical proofs and neural measurements.


## Finite certificate scope

MathCan/CausalSubspaceCompression.lean is an Init-only finite register example.
It proves that deleting an inert fourth coordinate preserves all phase and output
traces, while erasing a deferred coordinate preserves the present observation
and can change the next one. It does not prove transformer properties or the
general analytical statements above. The finite Gramian identity is the exact
diagonal example diag(1,2) perturbed by diag(0,1), saturating the stated bound.

The independent Fraction-based oracle suite passes eight tests, including 300
seeded exact quotient-rank cases. Local Lean is unavailable; kernel verification
is delegated to the dedicated draft-PR workflow and must be reported separately.

Applied source: MoralityLabAI/LoopedTransformers, branch
feat/spc09-causal-reasoning-subspaces. Original frozen checkpoint results remain
unmeasured until the external SPC-04 archive is located.

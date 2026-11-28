# NRF-10: finite-rank projector leakage geometry and motion certificates

Date: 2026-11-15. This note isolates elementary but useful Grassmannian and operator-norm identities for leakage-aware compact observers. All priority claims are **project-specific synthesis**. Orthogonal projections, submultiplicative matrix norms and Grassmannian optimization are classical.

## Gram decomposition for an orthogonal observer

Let U ∈ ℝ^{d×k} have orthonormal columns (UᵀU=I_k), let P=UUᵀ and Q=I−P, and let J∈ℝ^{d×d} be any local recurrent Jacobian, including nonnormal and nonsymmetric examples. Define the local dark-to-observed leakage

\[
 L_J(P)=\frac1{\sqrt{k}}\|U^\top JQ\|_F
       =\frac1{\sqrt{k}}\|PJQ\|_F.
\]

Because the two right-factor subspaces P and Q are orthogonal, 

\[
 \boxed{\;kL_J(P)^2=\|U^\top J\|_F^2-\|U^\top JU\|_F^2\; }.
\]

**Proof.** Decompose UᵀJ=UᵀJP+UᵀJQ. The Frobenius inner product of the summands vanishes: tr(UᵀJPQJᵀU)=0. The first component has squared Frobenius norm ||UᵀJU||²_F because right multiplication by Uᵀ is an isometry of row vectors in ℝᵏ. Pythagoras gives the identity. In projector coordinates this is ||PJQ||²_F=||PJ||²_F−||PJP||²_F.

For k=1, write U=u and observe that

\[
 L_J(P)^2=u^\top JJ^\top u-(u^\top Ju)^2.
\]

The Euclidean gradient of this ambient polynomial is 2JJᵀu−2(uᵀJu)(J+Jᵀ)u. Projecting onto the tangent of the unit sphere gives its intrinsic gradient. This is a computable objective for nonnormal dynamics and a useful oracle for numerical autodifferentiation.

## Projector motion bound

For a second rank-k orthogonal projector P′, set Δ=P′−P and Q′=I−P′. The exact transport-of-observation difference is

\[
 P'JQ'-PJQ = \Delta JQ' - PJ\Delta.
\]

Using the Frobenius/operator submultiplicativity and ||P||op=||Q′||op=1,

\[
 \boxed{\;|L_J(P')-L_J(P)| \le \frac{2\|J\|_{op}}{\sqrt{k}}\|P'-P\|_F.\;}
\]

Averaging over shadow states J₁,…,Jₙ gives the same bound with the mean Jacobian operator norm. If ||J_i||op is unavailable, the larger Frobenius norm gives a conservative measurable certificate. The projector displacement can be calculated without materializing d×d matrices:

\[
 \|UU^\top-VV^\top\|_F^2=2\bigl(k-\|U^\top V\|_F^2\bigr).
\]

The bound constrains leakage under small subspace changes and is not a guarantee that optimization decreases leakage. In NRF-10 the learned projectors can move a substantial distance; the measured improvement is empirical.

## Jensen gap between training and evaluation penalties

NRF-10 optimizes the average over calibration states of L_J(P)², while the earlier NRF protocol evaluates (average L_J(P))². For the finite nonnegative local leakages ℓ₁,…,ℓₙ,

\[
 \underbrace{\frac1n\sum_i\ell_i^2}_{\mathrm{training\ penalty}}-
 \underbrace{\left(\frac1n\sum_i\ell_i\right)^2}_{\mathrm{reported\ penalty}}
 = \frac1n\sum_i (\ell_i-\overline\ell)^2\ge0.
\]

Thus the calibrated loss penalizes the original evaluation metric and its per-state dispersion. Selecting γ with independent fold-9 task labels reduces the risk of choosing it directly on the sealed fold-10/11 outcomes.

## Exact tests and formal boundary

- `projector_leakage_geometry.py` uses `Fraction` for full-dimensional rational matrices and gives exact Gram identities and conservative projector-motion checks.
- `tests/test_projector_leakage_geometry.py` checks 1,200 rank-one rational projector/Jacobian triples, 462 Jordan shear configurations, one 3D projector example, exact Jensen values and failure cases.
- `MathCan/ProjectorLeakage.lean` verifies two Nat semiring squared-channel expansions and a zero-injection identity. The real-valued Gram, operator norm and Grassmannian results remain written proofs supported by rational tests; they are **not** proved in Lean.

Application: MoralityLabAI/LoopedTransformers PR #95. On twelve frozen ToyLoop checkpoints, the joint rank-eight task/leakage observer reduced the held-out combined objective against an equal-budget task-only observer in all twelve cells, and the preregistered depth-32 compound gate passed on five of six seeds. The observation map, not the original neural network, was changed.

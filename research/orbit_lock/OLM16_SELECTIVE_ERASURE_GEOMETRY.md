# OLM-16: Minimum-norm selective feature erasure and tangent controls

November 16, 2026. Exact mathematical companion to [SMC-16 selective active feature kill](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc16-selective-feature-kill-20261116/research/real_recurrence_sae_v1/SMC16_PROTOCOL.md), continuing [OLM-15](OLM15_NATIVE_SAE_ERASURE.md). All proofs here are elementary finite-dimensional linear algebra and second-order calculus. They are expressed under the explicit assumptions below and tested by independent rational witnesses. They are **written proofs rather than Lean kernel formalizations**.

## OLM-16A: Unique least-norm change of one active affine coordinate

Let V be a real Euclidean inner-product space of dimension d. Choose nonzero affine feature covectors a, o_1, ..., o_q ∈ V and a positive target displacement b. The q "other active features" are represented by linearly independent covectors, collected as the q×d row matrix O. Define

\[
P=I-O^\top(OO^\top)^{-1}O,\qquad v=Pa.
\]

**Theorem 16A.** If v≠0, the constrained affine edit

\[
O\delta=0,\qquad a^\top\delta=b
\]

has the unique minimum-L2-norm solution

\[
\boxed{\delta_*=\frac{b}{\|v\|^2}v,\quad \|\delta_*\|=\frac{b}{\|v\|}.}
\]

**Proof.** P is the orthogonal projector onto ker(O). Every feasible δ lies in ker(O); consequently aᵀδ=vᵀδ=b. Cauchy–Schwarz implies b≤‖v‖‖δ‖, with equality precisely when δ is a positive scalar multiple of v. The stated δ_* meets both constraints and attains the lower bound. Uniqueness follows from equality in Cauchy–Schwarz.

**Rank obstruction.** If v=0, then a lies in the row span of O, implying aᵀδ=0 for every δ∈ker(O). For b>0 the selective edit is impossible. If O has deficient row rank, the displayed inverse does not exist; SMC-16 abstains rather than applying a numerically unstable pseudoinverse. This is an operational identifiability obstruction from a fixed encoder Jacobian.

For the frozen SAE top-four ReLU code, a=w_j ⊘ scale and O contains the other three active physical encoder rows. Let z_j>0 be the clean feature coefficient and τ>0 a frozen overshoot. Setting b=z_j+τ moves the selected affine preactivation exactly to −τ while leaving the other three affine preactivations unchanged, under the active-cell linear formula. The SMC-16 registered parameters are τ=0.02 and a maximal dose of 6 times the corresponding native SAE decoder contribution norm.

## OLM-16B: Equal-dose tangent sham

Let A be the 4×d matrix collecting all four active encoder covectors, and suppose rank(A)=4<d. Its kernel has dimension d−4≥1, so it contains vectors t satisfying

\[
At=0,\qquad \|t\|=\|\delta_*\|.
\]

**Theorem 16B.** Along the physical edit h−t, all four original affine SAE preactivations are unchanged exactly. This follows directly from each row of A annihilating t. For a ReLU top-k encoder, invariance of the **reported selected activations** additionally requires that the original four atoms remain selected; a previously inactive row can change and enter top-k. SMC-16 therefore checks the unmodified full SAE re-encoding for both edit arms and labels failures as abstentions before observing task margins.

The nullspace sham controls for displacement norm while preserving the chosen **local** active affine coordinates. It need not control changes in previously inactive features, the downstream model's latent geometry, or all unobserved task-relevant coordinates.

## OLM-16C: Sharp second-order bound for selective kill versus tangent sham

Let m:V→R be twice continuously differentiable along both edit segments from the same clean state h, and assume ‖D²m‖op≤M on both. Write

\[
L(\delta)=m(h)-m(h-\delta),\quad
d=L(\delta_*)-L(t),\quad
\|\delta_*\|=\|t\|=r.
\]

**Theorem 16C.**
\[
\boxed{|d-Dm(h)[\delta_*-t]|\le Mr^2.}
\]

**Proof.** Taylor expansion of each branch yields L(δ)=Dm(h)[δ]+e(δ), with |e(δ)|≤M‖δ‖²/2. Subtraction and the triangle inequality give the displayed bound. Equality is attainable: in R³ with h=0, δ_*=r e₁, t=r e₃, and m(x)=M(x₁²−x₃²)/2, the linear term vanishes and the absolute effect difference is Mr². Thus the coefficient cannot be improved without additional curvature structure.

A measured positive d may arise from a first-order task gradient aligned with the selective direction or from finite-radius curvature. A formal local derivative claim needs an independent Hessian certificate. The hosted SMC-16 test is numerical FP64 recurrence, and does not claim such a certificate.

## OLM-16D: Active selection plus exact selective erasure does not entail functional necessity

Take h=(1,1,1), selected feature a=e₁ and other preserved active feature o=e₂. The minimum-norm erasure δ_*=e₁ silences the selected coordinate while preserving o; an equal-norm tangent sham t=e₃ preserves both. Let the task margin be m(x)=10+x₂. Both edits leave m unchanged. The selected atom is positive before the intervention, and it is selectively erased after the intervention, yet its removal has zero task effect. Exact feature selection, local selectivity and task necessity are logically distinct properties.

## Applied falsification contract

SMC-16 fixes all frozen SMC-13C cross-teacher permutations on their original calibration cohort and evaluates four source-A-to-independent-B target SAE pairs on two new 64-puzzle cohorts. On the receiving model, the source-matched atom must be one of four naturally active top-k atoms. The physical encoder projector silences it with a small −τ overshoot, preserves other active clean coefficients within 1e−4 after full re-encoding, and rejects edits over the original six-times-native dose cap. A seeded tangent edit at the same dose preserves the original four selected coefficients under the same re-encoding test.

The primary task estimand is the difference in correct-digit margin drops between selective kill and tangent sham. Its acceptance gate uses independently clustered puzzle bootstraps and clean-correct-to-wrong flip counts. Any empirical success is conditional on this explicit causal edit and its eligibility coverage. The proven mathematical statements concern affine encoder geometry and smooth task-margin response bounds, and do not assert a hidden shared Sudoku reasoning circuit.

# OLM-18: Causal gradient duality and curvature under inactive SAE leakage

November 16, 2026. Exact mathematical companion to the prospectively registered [SMC-18](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc18-gradient-leakage-20261116/research/real_recurrence_sae_v1/SMC18_PROTOCOL.md), extending [OLM-17's inactive-preactivation matching obstruction](OLM17_INACTIVE_ENCODER_CONTROL.md). These are original **applications and explicit witnesses** of classical finite-dimensional Hilbert-space linear algebra and multivariable Taylor calculus. Statements below have proofs and independent standard-library exact-Fraction tests. They are not Lean kernel formalizations.

## OLM-18A: Every physical task gradient has a minimum-norm inactive-feature dual

Let B∈R^{p×d} be the physical encoder covectors of the *initially inactive* sparse-autoencoder atoms, with **full column rank d**. For SMC-18 p=92 and d=48. Let g∈R^d be the true differentiable task-margin gradient at one clean recurrent stage-one token.

**Theorem.** There is a unique minimum-Euclidean-norm coefficient vector λ*∈R^p satisfying Bᵀλ*=g, namely

\[
\boxed{\lambda_* = B(B^\top B)^{-1}g,\qquad
 \|\lambda_*\|^2=g^\top(B^\top B)^{-1}g.}
\]

For every physical hidden edit u∈R^d,

\[
\boxed{g^\top u=\lambda_*^\top B u,\qquad
|g^\top u|\le\|\lambda_*\|\,\|B u\|.}\tag{1}
\]

**Proof.** BᵀB is positive definite under the full-column-rank hypothesis, and direct multiplication verifies Bᵀλ*=g. Any other solution is λ*+w with Bᵀw=0; since λ* lies in col(B), it is orthogonal to ker(Bᵀ). Pythagoras gives ‖λ*+w‖²=‖λ*‖²+‖w‖². The identity and bound (1) follow by substitution and Cauchy–Schwarz. The constant is sharp, e.g. B=I and u=g.

**Interpretation.** On any frozen state with full rank B, *every* physical task-gradient contribution can be expressed by the originally inactive SAE preactivation shifts, even when the causally selected atom is one of the four active ones. Representability is therefore **a gauge ambiguity**, not proof that the teacher computes its task via inactive SAE features. To claim specific feature mediation, a further independent intervention or structural assumption is necessary.

The Frobenius and singular-value bounds give ‖λ*‖≤‖g‖/σ_min(B). If the smallest singular value is small, the inactive dual can be ill-conditioned. The SMC-18 receipt must report its actual singular-value floor and reconstruction residual.

## OLM-18B: Orthogonal selective kill and tangent sham

Let A∈R^{4×d} have full row rank, representing all four originally active encoder covectors. Let the selective physical kill k be the unique minimum-norm solution of Ak=b e_j with b>0, as in OLM-16. Let its equal-dose tangent sham s satisfy As=0 and ‖k‖=‖s‖=r.

**Theorem.** k lies in row(A) while s lies in ker(A), hence

\[
\boxed{\langle k,s\rangle=0,\quad
\|k-s\|^2=2r^2,\quad
 g^\top(k-s)=g^\top k-g^\top s.}\tag{2}
\]

The decomposition is exact for the chosen physical model and local SAE coordinate constraints. Its interpretation as *feature-specific* mediation requires control of downstream sensitivity to the other 92 encoder rows.

## OLM-18C: Equal-dose finite task-margin discrepancy

Let m be twice continuously differentiable along h−tk and h−ts, with \(\|D^2m\|_{\mathrm{op}}\le M\) along both segments. Set \(D=m(h-s)-m(h-k)\), \(g=Dm(h)\), and \(\|k\|=\|s\|=r\).

**Theorem.**

\[
\boxed{|D-g^\top(k-s)|\le Mr^2.}\tag{3}
\]

**Proof.** Taylor's formula yields \(m(h-v)=m(h)-g^\top v+R_v\), \(|R_v|\le M\|v\|^2/2\). Subtract the two expansions and apply the triangle inequality. The constant is sharp for equal-norm orthogonal edits with the quadratic \(m(x)=(M/2)(x_1^2-x_2^2)\) at h=0, k=r e₁, s=r e₂, where the linear prediction vanishes and |D|=Mr².

When a common Hessian H at h and a third derivative bound T are additionally verified along both segments,

\[
\boxed{\left|D-\left[g^\top(k-s)-\tfrac12(k^\top Hk-s^\top Hs)\right]\right|
\le \tfrac13 Tr^3.}\tag{4}
\]

The one-dimensional third-order remainders each have magnitude ≤Tr³/6. This constant is sharp on the orthogonal two-coordinate cubic \(m(x)=T(x_1^3-x_2^3)/6\) with h=0, k=r e₁, s=r e₂, where the first and second derivatives vanish and D=Tr³/3.

SMC-18 measures *numerical FP64* gradients and central directional curvatures and compares finite D with the first- and second-order predictions. Its estimates are **not** interval-verified Hessian or third-derivative bounds, so equations (3) and (4) are conditional theorems rather than certificates for those checkpoints.

## OLM-18D: Identical local gradients and Hessians can hide opposite finite effects

Take h=0, k=e₁, s=e₂, and clean positive true-digit margins

\[
m_A(x)=10+x_1,\qquad m_B(x)=10+x_1-3x_1^3.
\]

Both functions have identical margin 10, gradient e₁, and zero Hessian at the clean state. Their finite paired effects differ:

\[
D_A=m_A(-e_2)-m_A(-e_1)=1,\quad
D_B=m_B(-e_2)-m_B(-e_1)=-2.
\]

Their margins remain positive on all edit segments \([-e_1,0]\) and \([-e_2,0]\). Thus exact clean first- and second-order task jets, clean classification and unchanged active/inactive encoder geometry do not identify the *sign* of the full finite intervention. The third-order remainder matters at these amplitudes. This strengthens OLM-14's injection-versus-erasure obstruction in the specific SMC-18 gradient-attribution setting.

## Registered applied contract

SMC-18 retains the original SMC-16 selective matched-feature kill and SMC-17 outcome-blind inactive-matched sham at equal physical dose. On fresh, source-disjoint noncanonical Sudoku cohorts (202618030000 and 202618040000, 64 puzzles each), it obtains the exact FP64 autograd gradient of the correct-digit-minus-frozen-clean-rival margin with respect to the clean stage-one goal-token hidden state. It records the measured finite effect D, first-order prediction L, local directional second-order diagnostic Q, full-rank inactive gradient dual λ*, inactive shift and task-gradient reconstruction, and puzzle-clustered acceptance gates. An independent stdlib auditor verifies the scalar recomputations and source hashes.

A positive gradient-predictive gate is evidence for a *local task-linear contribution of the specified physical hidden edit* in the tested checkpoint family. Full-rank inactive encoder rows prevent a uniquely identified SAE semantic mediation claim from following solely from that evidence.

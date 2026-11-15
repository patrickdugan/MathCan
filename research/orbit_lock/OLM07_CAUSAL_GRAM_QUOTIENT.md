# OLM-07: Causal Gram geometry on a recurrent gauge quotient

**November 15, 2026.** Pure mathematical companion to [SMC-07's actual pretrained recurrent SAE experiment](https://github.com/MoralityLabAI/Compactification-Theory/pull/151). It continues OLM-01–06's theme of task-relative quotients and gauge-invariant latent structure. The historical motivation remains OpenAI Mathematics #131 (degree-preserving graph switching) and #238 (permutation mixing); the deductions below are independent linear-algebra and Taylor arguments, not consequences imported from those preprints. Priority relative to the broader literature is not established.

## 1. Observational gauge and the causal feature operator

Fix a finite family of recurrent states \(h_i\in\mathbb R^d\) with positive weights \(w_i\), \(\sum_iw_i=1\), and a differentiable future-output map \(F_i:\mathbb R^d\to\mathbb R^{q_i}\). Each map represents a frozen teacher continuing from that state for a declared horizon and reading a particular output. Put \(J_i=DF_i(h_i)\).

Define the common first-order observational-gauge subspace

\[
G=\bigcap_i \ker J_i,\qquad
H=\sum_iw_i J_i^\top J_i .
\]

For a dictionary \(D\in\mathbb R^{d\times m}\), its columns are feature directions \(d_j\). Define the **causal Gram matrix**

\[
\boxed{C_D=D^\top H D
=\sum_i w_i (J_iD)^\top(J_iD).}
\tag{1}
\]

**Theorem OLM-07A (exact quotient, positive energy and rank).** The matrix \(C_D\) is positive semidefinite and

\[
\boxed{z^\top C_Dz=\sum_iw_i\|J_iDz\|_2^2,\quad
\ker H=G,\quad
\operatorname{rank}C_D\le\min(m,d-\dim G).}
\tag{2}
\]

If every column of a matrix \(Q\in\mathbb R^{d\times m}\) belongs to \(G\), then

\[
\boxed{C_{D+Q}=C_D.}\tag{3}
\]

**Proof.** Expand the quadratic form to obtain the first equality; its summands are nonnegative. The equality \(v^\top H v=\sum_iw_i\|J_i v\|^2\) and strictly positive weights show \(Hv=0\) precisely when all \(J_iv=0\). Thus \(\ker H=G\). Rank follows by factoring \(H^{1/2}D\) and using rank-nullity. If \(J_iQ=0\), then \(J_i(D+Q)=J_iD\) at every sample and (3) follows. QED.

For a *single* selected output Jacobian, the quotient has dimension at most its output rank. Across multiple contexts, rank may grow: a different local gauge kernel for every puzzle need not define a large common subspace.

## 2. Representation changes and codebook gauges

For any invertible feature-coordinate change \(B\in\mathbb R^{m\times m}\),

\[
\boxed{C_{DB}=B^\top C_D B.}\tag{4}
\]

If the new coordinate is \(z'=B^{-1}z\), the physical intervention is unchanged: \(DBz'=Dz\). Thus \(z'^\top C_{DB}z'=z^\top C_Dz\).

For an orthogonal signed permutation \(P\), (4) is an orthogonal similarity and preserves the causal Gram eigenvalues. Under a general invertible B, quadratic energies remain invariant under the appropriate coordinate change, while the *individual eigenvalues* need not be invariant. A sparse top-k code typically preserves its structure only under signed permutations satisfying the activation convention; signed flips can alter nonnegative ReLU codes, so ordinary permutations are the natural SAE feature-label gauge.

This theorem suggests studying the spectrum and intervention energies of a latent dictionary rather than assuming arbitrary SAE feature indices carry a common identity between checkpoints. It also warns that equal spectra do not establish an atom-by-atom alignment.

## 3. Finite-radius interventions and a quantitative certificate

Assume each \(F_i\) is twice continuously differentiable on every line segment \(h_i+t\,r\,d_j\), \(0\le t\le1\), with Hessian operator norm bounded by \(M\). Let each dictionary column have Euclidean norm at most one, and assume \(\|J_i\|_{\mathrm{op}}\le L\).

For \(r>0\), measure the directional finite difference

\[
\Delta_{ij}(r)=\frac{F_i(h_i+r d_j)-F_i(h_i)}{r}.
\]

Define its finite-difference causal Gram

\[
\widehat C_{jk}(r)=\sum_i w_i\langle\Delta_{ij}(r),\Delta_{ik}(r)\rangle.
\]

**Theorem OLM-07B (finite-radius causal Gram error).** For every pair of feature columns,

\[
\boxed{
|\widehat C_{jk}(r)-(C_D)_{jk}|
\le M L r+\frac{M^2r^2}{4}.
}
\tag{5}
\]

Consequently, for a dictionary of m features,

\[
\boxed{\|\widehat C(r)-C_D\|_{\mathrm{op}}
\le m\left(MLr+\frac{M^2r^2}{4}\right).}
\tag{6}
\]

**Proof.** Taylor's integral remainder applied to each segment gives
\(\Delta_{ij}(r)=J_i d_j+e_{ij}\) with
\(\|e_{ij}\|\le Mr/2\). Expanding the two inner products yields the two cross terms and one error-product term. Their magnitudes are bounded by \(2(L)(Mr/2)+(Mr/2)^2\), proving (5) after taking the weighted average. The spectral norm is bounded by the maximum absolute row sum of the symmetric difference matrix, giving (6). QED.

If the Hessian bound M and Jacobian bound L are *certified on the measured state segments*, then Weyl's eigenvalue inequality gives an explicit spectral uncertainty interval around every empirically measured causal Gram eigenvalue. The SMC-07 experiment reports finite-radius output changes but has **not established such local M,L enclosures**, so its intervention measurements are evidence rather than a kernel-level causal-spectrum certificate.

### OLM-07C. Quotient directions can be second-order visible

For \(F(x,y)=x+\tfrac a2y^2\) at the origin, \(J=(1,0)\) and the direction \(e_y\) belongs to its first-order kernel. Yet

\[
F(0,r)-F(0,0)=\tfrac a2r^2.
\]

The Hessian norm bound \(M=|a|\) is attained in the Taylor remainder. Hence a Jacobian-null direction is *only first-order neutral* unless an exact symmetry or a stronger invariant is proved. Conversely, \(F(x,y)=x\) has an exact full-line gauge in the y direction: its output is unchanged for perturbations of any magnitude along that coordinate.

## 4. Reconstruction MSE and output fidelity are different geometries

Two hidden reconstruction errors can have opposite order under Euclidean norm and downstream causal effect. In the linear example \(F(x,y)=x\), error \(u=(0,N)\) has squared hidden norm \(N^2\) and zero output error, while error \(v=(\varepsilon,0)\) has squared norm \(\varepsilon^2\) and nonzero output error \(\varepsilon^2\). Taking \(N>\varepsilon>0\) reverses the reconstruction-error ranking.

More generally, local linear output error is \(e^\top H e\), while hidden reconstruction error is \(\|e\|^2\). The two rank different errors unless \(H\) is proportional to identity on the relevant subspace. Sparse autoencoders trained only for reconstructing activations therefore need a separate causal intervention evaluation.

## 5. Application to the source-locked SMC-07 experiment

[SMC-07](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc07-real-trm-sae-20261115/research/real_recurrence_sae_v1/SMC07_RESULTS.md) uses the independently pretrained 44,001-parameter TRM-inspired Sudoku recurrence. For 16 heldout puzzle IDs, it measures equal-L2-radius interventions on selected learned SAE decoder atoms versus inactive-atom, isotropic and remote-token controls, averaging across three independently fit SAE seeds within each heldout puzzle.

The measured mean difference in final goal-logit norm at radius 0.2, active SAE minus isotropic, is +0.10247, with descriptive 95% puzzle-bootstrap interval [0.05956,0.14785]; active minus inactive is +0.06260 [0.02535,0.10328]. This is **causal sensitivity**, not a claim that an SAE atom represents a particular symbolic Sudoku proposition.

The exact FP64 channel-common shift at the *stage-two pre-LayerNorm2 bus* has an observed final-logit difference below \(1.4\cdot10^{-15}\). This is a source-specific example of a structurally known gauge direction. Theorem OLM-07A explains why dictionary atoms differing only by such a gauge direction cannot be distinguished by the corresponding local output Jacobian. The SMC-07 feature interventions happen at a **different interface** (stage-one post-block state), so the same gauge equation cannot be assumed there.

## Verification and continuation

The standard-library [exact rational oracle](causal_gram.py) checks gauge-invariant Gram calculations, change-of-coordinates congruence and the sharp quadratic Taylor witness. [Regression tests](../../tests/test_causal_gram.py) exercise these finite identities. These are illustrative computations of the stated linear-algebra proofs, not a Lean kernel formalization.

A future local-autograd/interval-Arb experiment could measure \(J_iD\), bound M on predeclared intervention tubes and estimate the feature-causal Gram with rigorous eigenvalue intervals. That would convert the measured SMC-07 sensitivity advantage into an auditable local functional-geometry statement.

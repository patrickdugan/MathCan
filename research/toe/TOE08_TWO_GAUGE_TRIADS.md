# TOE-08C: Two Yang–Mills triads, bivector Gram rank and a dynamical cone-matching obstruction

**Status: 2026-11-11.** A concrete, minimally coupled two-SU(2)-Yang–Mills matter action is reduced on a spatially flat FLRW geometry. We compute its complete *minimal* stress-energy tensor and homogeneous gauge equations. A separate, explicitly assumed observer-frame positive bivector Gram map is tested as a possible GfE 2-form constitutive response. The exact six-by-six rank and mixed-block dynamics yield a new conditional obstruction: an initially diagonal, cone-matched response in the symmetric two-triad family becomes mixed at first order under ordinary Yang–Mills evolution. A self-consistent **Einstein–Yang–Mills** example verifies this happens even when the background Friedmann constraint and Raychaudhuri equation hold.

**Physics boundary.** This is a candidate *source laboratory* for the multi-multiplet escape highlighted by [Pereira, *Gravitational Waves and Matter Constraints in Gravity from Entropy* (2026)](https://arxiv.org/abs/2609.03082), and a follow-up to [MathCan TOE-07](TOE07_MULTIPLET_CONE_AND_COVARIANT_COMPLETION.md). Bianconi's [Λ-Gravity from Entropy (2026)](https://arxiv.org/abs/2610.34496) uses a particular Dirac–Kähler induced matter metric, whose exact 2-form embedding and metric variation have **not** been identified with the positive Gram ansatz here. The SU(2) internal triplet is different from a *single foundational Dirac–Kähler multiplet* in Pereira's rank theorem. The homogeneous isotropic gauge ansatz is standard; see [Maleknejad and Sheikh-Jabbari, *Non-Abelian Gauge Field Inflation* (2011)](https://arxiv.org/abs/1102.1932). The present determinant and dynamical-matching tests are MathCan derivations within the stated model.

## 1. Concrete two-multiplet matter action

Let \(I=1,2\) index independent SU(2) factors, and \(a=1,2,3\) their adjoint indices. With signature \((-+++)\), use the *minimal* Yang–Mills action

\[
S_{\rm YM}=-\frac14\int\sqrt{-g}\sum_{I=1}^{2}\sum_{a=1}^{3}
  F_{I\mu\nu}^{a}F_I^{a\mu\nu}\,d^4x,\quad
F^a_{I\mu\nu}=\partial_\mu A^a_{I\nu}-\partial_\nu A^a_{I\mu}
+g_I\epsilon^{abc}A^b_{I\mu}A^c_{I\nu}.
\]

On \(ds^2=-dt^2+a(t)^2d\mathbf x^2\) with \(A^a_{I0}=0\) and \(A^a_{Ii}=a\psi_I(t)\delta^a_i\), the physical fields are

\[
 E_I=\dot\psi_I+H\psi_I,\qquad B_I=g_I\psi_I^2.
\]

The Lagrangian per comoving volume is \(\frac32a^3\sum_I(E_I^2-B_I^2)\). Varying \(\psi_I\) yields the homogeneous Yang–Mills equations

\[
\boxed{\dot\psi_I=E_I-H\psi_I,\qquad
\dot E_I=-2HE_I-2g_I^2\psi_I^3.}\tag{1}
\]

The *complete stress tensor for this minimally coupled action* is

\[
T_{\mu\nu}^{\rm YM}=\sum_{I,a}\left(F^a_{I\mu\rho}F_{I\nu}^{a\;\rho}
-\tfrac14g_{\mu\nu}F^a_{I\rho\sigma}F_I^{a\rho\sigma}\right).
\]

Direct orthonormal-frame contraction gives

\[
\boxed{T_{\hat\mu\hat\nu}=\operatorname{diag}(\rho,p,p,p),\quad
\rho=\frac32\sum_I(E_I^2+B_I^2),\quad p=\rho/3.}\tag{2}
\]

Equation (1) implies \(\dot\rho+4H\rho=0\) exactly. `stress_tensor` independently constructs all \(4\times4\) components from the field strengths, with rational arithmetic. The model has no separate scalar inflaton or axion, unlike gauge-flation models with additional operators.

## 2. The full 6×6 observer-frame constitutive matrix

At each time choose the comoving orthonormal frame. Flatten a 2-form in the order \((01,02,03,23,31,12)\), with its electric and magnetic amplitudes regarded as spatial triples. **Define**, as a candidate constitutive tensor,

\[
 M_{AB}=\sum_{I,a}\mathcal F^{Ia}_A\mathcal F^{Ia}_B,
 \qquad \mathcal F^{Ia}=(E_I\mathbf e_a,B_I\mathbf e_a).
\]

This is an observer-relative **positive Gram** prescription. It is an explicit choice, pending comparison with Bianconi's true induced metric, whose Lorentzian index placement may change the signs. The six-dimensional response takes the isotropic form

\[
\boxed{M=\begin{pmatrix}m_E I_3&cI_3\\cI_3&m_B I_3\end{pmatrix},\qquad
 m_E=\sum_I E_I^2,\quad m_B=\sum_I B_I^2,\quad c=\sum_I E_IB_I.}\tag{3}
\]

This includes the **mixed electric–magnetic block** omitted by a diagonal-only \(m_E,m_B\) parametrization. Every eigenvalue of its repeated 2×2 block is nonnegative. The complete six-dimensional determinant is

\[
\boxed{\det M=(m_Em_B-c^2)^3=(E_1B_2-E_2B_1)^6.}\tag{4}
\]

*Proof:* the 6×6 matrix consists of three identical 2×2 blocks after permuting basis vectors. Cauchy–Binet in two dimensions yields \(m_Em_B-c^2=(E_1B_2-E_2B_1)^2\). Thus the response has full rank exactly when the two gauge-multiplet vectors \((E_1,B_1)\) and \((E_2,B_2)\) are linearly independent. One such triplet alone produces rank at most three in this particular Gram model. The executable oracle separately computes a six-dimensional rational determinant on 140 seeded two-multiplet configurations.

### A specified curvature-response probe, with Lorentzian signs

For comparison, if a separate nonminimal action is **defined** by

\[
S_{\rm probe}=\frac\lambda4\int\sqrt{-g}\,
R_{\mu\nu\rho\sigma}\sum_{I,a}F_I^{a\mu\nu}F_I^{a\rho\sigma}\,d^4x,
\]

then differentiation with respect to independent curvature **pair-matrix entries**, holding the metric and gauge field strengths fixed, gives a raw pair response proportional to

\[
\boxed{P_{IJ}=\lambda\begin{pmatrix}m_EI_3&-cI_3\\-cI_3&m_BI_3\end{pmatrix}.}\tag{5}
\]

The opposite mixed-block sign comes from raising the temporal index of \(F^{0i}\). This is the full displayed 6×6 **raw pair-response matrix** of the stipulated probe term, with its index-counting normalization stated in the implementation. Algebraic Riemann/Bianchi projection, the full metric variation including \(\nabla\nabla P\), and the Yang–Mills equation modified by nonzero \(\lambda\) remain to be derived before studying a coupled solution. Equations (1)–(2) describe the **minimal \(\lambda=0\)** dynamics. Equation (5) is a curvature susceptibility that can be probed at fixed fields; it cannot be included in the dynamics without re-deriving the equations.

## 3. Matching the diagonal tensor response

Continue the explicitly **assumed** constitutive map from TOE-07:

\[
\Theta=I_6+\alpha M-\beta\operatorname{diag}(2AI_3,2BI_3),\quad
A=H^2+\dot H,\quad B=H^2+K/a^2.
\]

Its repeated 2×2 block has diagonal entries \(\theta_E=1+\alpha m_E-2\beta A\) and \(\theta_B=1+\alpha m_B-2\beta B\), and mixed entry \(\alpha c\). Positive definiteness requires \(\theta_E>0\) and \(\theta_E\theta_B-\alpha^2c^2>0\); the exact inverse is

\[
\Theta^{-1}_{\rm block}=\frac1{\theta_E\theta_B-\alpha^2c^2}
\begin{pmatrix}\theta_B&-\alpha c\\-\alpha c&\theta_E\end{pmatrix}.
\]

Equal diagonal entries impose the TOE-07/Pereira-style response equation

\[
\boxed{\alpha(m_E-m_B)=2\beta(\dot H-K/a^2).}\tag{6}
\]

The simpler **diagonal-block characteristic argument** additionally assumes \(c=0\). For \(c\ne0\), the coupled E/B bivector response is mixed and its true principal symbol must be recomputed. Consequently, a nonzero \(c\) is a failure of that simplifying assumption, **not** a demonstrated absence of real characteristics in the mixed theory.

## 4. Mixed-response dynamical obstruction for the symmetric pair

Define \(S=m_E-m_B\) and \(c=\sum E_IB_I\). Differentiating with the exact Yang–Mills equations (1) gives

\[
\begin{aligned}
\dot S&=-4HS-8\sum_I g_I^2\psi_I^3E_I,\\
\dot c&=-4Hc+2\sum_I g_I\psi_I(E_I^2-B_I^2).
\end{aligned}\tag{7}
\]

Take **two** identical couplings and magnetic backgrounds, with opposite physical electric fields:

\[
\psi_1=\psi_2=\psi\ne0,\quad g_1=g_2=g>0,\quad
E_1=e,\quad E_2=-e.
\]

Then \(c=0\), \(m_E=2e^2\), \(m_B=2g^2\psi^4\), and

\[
\boxed{\dot c=4g\psi(e^2-g^2\psi^4)=2g\psi S.}\tag{8}
\]

If Eq. (6) holds with \(K=0\),

\[
\boxed{\dot c=\frac{4\beta g\psi}{\alpha}\dot H.}\tag{9}
\]

For \(\alpha,\beta,g>0\), \(\psi\ne0\) and \(\dot H\ne0\), it is **impossible** for both the diagonal cone match and the vanishing mixed block to persist even to first order under the **minimal Yang–Mills equations**. This is a conditional dynamical statement for the symmetric doublet. It is not a general two-multiplet GfE no-go theorem.

## 5. An exactly consistent GR+YM initial background

Use rational dimensionless values

\[
\beta=\frac1{100},\quad\alpha=\frac3{50},\quad
H=1,\quad g=1,\quad \psi=\frac14,\quad
(e_1,e_2)=\left(\frac1{32},-\frac1{32}\right).
\]

Then

\[
m_E=\frac1{512},\quad m_B=\frac1{128},\quad c=0,\quad
S=-\frac3{512},\quad \dot H=-\frac9{512}.
\]

This is **compatible with the ordinary Einstein–Yang–Mills equations** with gravitational coupling \(\kappa=9/5\) and a constant cosmological term \(\Lambda=3045/1024\). Indeed

\[
\rho=\frac{15}{1024},\quad
3H^2=\Lambda+\kappa\rho,\quad
\dot H=-\frac\kappa2(\rho+p)=-\frac9{512}.
\]

At this event the diagonal response difference is zero, and \(\alpha c=0\), while its exact initial derivative is

\[
\boxed{\dot c=-\frac3{1024},\qquad
\frac d{dt}(\alpha c)=-\frac9{51200}.}\tag{10}
\]

A subtlety: in this symmetric example the first time derivative of **diagonal matching error** is also zero. With a radiation-like stress tensor, Einstein's equations imply \(\ddot H=-4H\dot H\); Eq. (7) gives \(\dot S=-4HS\) initially. Hence \(d(\alpha S-2\beta\dot H)/dt=0\), while the mixed response starts running. This means diagonal cone matching can look dynamically stable to first order even though the full response matrix has departed from the diagonal ansatz.

An independent rational RK4 step on the *coupled* Einstein–Yang–Mills equations confirms the sign and first derivative of the mixed block and preserves \(3H^2-\kappa\rho=\Lambda\) to high order. That integration is a diagnostic in GR and is **not** a numerical solution of full ΛGfE plus nonminimal gauge coupling.

## 6. Verification ledger and remaining physics

`yang_mills_triads.py` computes the exact matter dynamics, all sixteen orthonormal-frame stress components, both Gram matrices, positive-sector constraints, their derivatives, and exact rational short-time integration. `tests/test_toe08_yang_mills.py` contains 26 test methods, including 140 independent 6×6 determinant trials, 150 energy-continuity trials, the raw Lorentzian response checks, exact initial-data verification, and a checked reproducibility fixture. `MathCan/TOEYangMills.lean` checks eight auxiliary integer identities that make the algebraic proof obligations explicit, with no unsupported claim of Lean-certified GfE field equations.

Run:

```sh
python -m unittest tests.test_toe08_yang_mills -v
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/TOEYangMills.lean
```

**Outstanding scientific gates:** (i) construct the exact Bianconi Dirac–Kähler 2-form matter tensor from a chosen fundamental multiplet action; (ii) retain the first Bianchi projection and covariant metric derivative of any curvature-coupled term; (iii) solve the resulting coupled GfE–matter equations rather than using the GR laboratory; (iv) derive the *complete* metric–matter characteristic polynomial, including mixed electric–magnetic blocks and gauge constraints, and test strong hyperbolicity and the kinetic signature within an explicit EFT cutoff. The simple diagonal TT polynomial from Pereira applies only under its stated isotropic-block and fixed-matter assumptions.

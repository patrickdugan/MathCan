# TOE-15: SO(2) tensor closure and two-multiplet curvature compensation

**November 12, 2026.** TOE-15 independently tests (i) the six-mode tensor *trial* of TOE-13 for residual SO(2) equivariance and (ii) an algebraic foundational two-multiplet witness for Pereira's rank and curvature-cone matching conditions.

**Primary sources:** [Bianconi, Gravity from entropy (2025)](https://doi.org/10.1103/PhysRevD.111.066001) and [Pereira, Gravitational Waves and Matter Constraints (2026)](https://borowiecki.dev/pdf/2609.03082), especially equations (18), (34)-(43). The trial two-SU(2) Yang–Mills matter action and the foundational Dirac–Kähler multi-form matter action are distinct theories. Their metric and matter perturbations must not be silently combined.

## T1. Helicity invariance and the real six-to-complex-three determinant identity

Use TOE-13's real six-mode basis \((h_+,h_\times,a_{1+},a_{1\times},a_{2+},a_{2\times})\). Homogeneous SU(2) color/spatial triads leave a diagonal SO(2) little group along a \(z\)-directed wave. Its generator is

\[
J=\mathrm{diag}(J_2,J_2,J_2),\quad J_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
\]

The new exact oracle checks, for the existing full 0/1/2-form-completed *trial* tensor matrix \(P(\omega)\), that \(P^\top=P\) and \([P,J]=0\). Every 2-by-2 species block is then \(aI_2+bJ_2\). Via the complex coordinates \(z_f=q_{f,+}+iq_{f,\times}\), the real Hessian is the realification of a complex Hermitian 3-by-3 matrix \(H_+\). Therefore

\[
\boxed{\det_{\mathbb R}P(\omega)=|\det_{\mathbb C} H_+(\omega)|^2=(\det H_+(\omega))^2.}
\]

The oracle evaluates the independent 6-by-6 rational determinant and 3-by-3 Gaussian-rational determinant at real rational frequencies. It also reconstructs the degree-at-most-eight complex determinant polynomial from nine nodes, checking five further frequencies. The real 6-by-6 determinant has degree at most sixteen and is the square of that polynomial in the declared tensor trial.

This isolates the spin-two representation internally. The complete source-defined multi-form matter action might carry additional helicity-two perturbations, which require an enlarged kinetic block. Neither equivariance nor the determinant-square identity certifies strong hyperbolicity.

## T2. Minimal-rank two-multiplet source response

For \(N\) foundational-type multiplets with each form sector contributing two outer products, the algebraic response has rank at most \(2N\). A nonzero isotropic response on one three-dimensional bivector triplet has rank three, making \(N=2\) the first multiplet count allowed by this bound, as Pereira notes in Eq. (38).

An exact algebraic witness is available in the basis \((E_x,E_y,E_z,B_x,B_y,B_z)\). Let \(u_1=u_2=e_{B_z}\), \(v_1=e_{B_x}\), \(v_2=e_{B_y}\), and \(\lambda=m^2+\xi R=2\). Then

\[
M_i=u_iu_i^\top+2v_iv_i^\top,\qquad
\boxed{M_1+M_2=\operatorname{diag}(0,0,0,2,2,2).}
\]

Each \(M_i\) has rank two; their sum has rank three and is isotropic on the magnetic triplet. This uses only pointwise independent algebraic slots for \(D\Phi_i,\Phi_i\). The next subsection constructs smooth local normal-coordinate field jets realizing these slots. Global isotropy, coupled constraints, and equations of motion remain unverified.

With the existing synthetic FLRW curvature values \(A_c=H^2+\dot H=2/5\), \(B_c=H^2=1\), and parameters \(\alpha=3/500,\beta=1/100\), the witness has \(m_E=0,m_B=2\) and

\[
\boxed{
\theta_E=1+\alpha m_E-2\beta A_c=\frac{124}{125},\quad
\theta_B=1+\alpha m_B-2\beta B_c=\frac{124}{125},\quad
\theta_s=1-\beta(A_c+2B_c)=\frac{122}{125}.
}
\]

It exactly meets Pereira's **necessary** curvature-response condition:

\[
\boxed{
m_E-m_B=\frac{2\beta}{\alpha}(A_c-B_c)=-2.
}
\]

Therefore the E and B inverse responses match at this synthetic off-shell point. If one retained only the curvature-response two-square TT polynomial of Pereira Eq. (18), it would reduce to a positive multiple of \((\omega^2-p^2)^2\). For dynamically active fundamental matter multiplets, additional mixed and matter Hessians must be derived first.

## T2a. Local Dirac–Kähler jets realize the outer-product slots

The truncated source derivative is \(D=P_F(d+\delta_D)P_F\). The algebraic witness in T2 has an explicit smooth *pointwise normal-coordinate* realization. In coordinates \((t,x,y,z)\), choose for both multiplets the one-form

\[
\omega_1=\omega_2=\frac12(x\,dy-y\,dx),\qquad d\omega_i=dx\wedge dy=e_{B_z}.
\]

At the coordinate origin choose constant two-form zeroth-order data

\[
\zeta_1=dy\wedge dz=e_{B_x},\qquad
\zeta_2=dz\wedge dx=e_{B_y},
\]

with their first derivatives set to zero and the scalar fields zero. At the point, the one-form values vanish, as does their coderivative \(\delta_D\omega_i\), since the first-derivative matrix is antisymmetric. The 1-form component of \(D\Phi_i\) also vanishes because the scalar gradients and derivatives of \(\zeta_i\) vanish. The only nonzero component of \(D\Phi_i\) is its bivector \(d\omega_i=e_{B_z}\).

Thus the exact differential map \(D\) realizes the specified \(u_i,v_i\) at an event, with \(M_{(0)}=M_{(1)}=0\) at that event. The oracle explicitly computes all six independent exterior-derivative entries and the scalar coderivative. This removes **local first-jet realizability** as an obstruction to the algebraic witness.

It does not produce homogeneous global fields on FLRW, SO(3) covariance of all coupled principal coefficients, an on-shell matter stress tensor or a solution of the Einstein/G-field equations. A globally symmetry-inheriting completion may be substantially harder: the two individual multiplets carry preferred spatial orientations even though their summed bivector response is isotropic at the selected event.

## T3. The exact detuning discriminant

Set \(m_B=2+\varepsilon,m_E=0\), \(\theta=\theta_E=124/125\), and hold \(\theta_s>0\). Then

\[
\theta_B=\theta+\alpha\varepsilon,\quad
W_E-W_B=\frac{\alpha\varepsilon}{\theta(\theta+\alpha\varepsilon)},\quad
\boxed{\Delta_x=-4W_s^2\frac{\alpha^2\varepsilon^2}{\theta^2(\theta+\alpha\varepsilon)^2}.}
\]

For any nonzero \(\varepsilon\) within the positive-denominator branch, the curvature-only two-square polynomial has negative discriminant. Exact cone matching is a codimension-one algebraic relation, not an open parameter region. This conclusion is scoped to that curvature subblock.

## T4. The constrained dynamics gate

Lapse, shift and ordinary longitudinal Yang–Mills gauge directions carry little-group helicities of magnitude at most one around an isotropic background. A diagonal-SO(3) color-locked gauge triplet has a spin-two fluctuation representation, so the TOE-13 tensor species are the appropriate channels to test. The SO(2) commutator is an exact check on their trial matrix, not a proof that a source-defined expanded action contains precisely these channels.

The TOE-13 algebraic auxiliary G-field Schur map remains valid when its response blocks are invertible. Pereira's Eqs. (41)–(43) relate the source formulation to its auxiliary mixed-order system. What remains is a full variation of a *single* foundational multi-form action, including the covariant \(D\Phi_i\) differential map, the new matter/helicity-two principal, and background equations. These produce the constrained dynamical pencil and test its real roots and uniform symmetrizer.

**Verification:** research/toe/helicity_constraint.py provides exact rational commutators, Gaussian 3-by-3 determinants, six-by-six determinant cross-checks and rank-two outer-product constructions. tests/test_toe15_helicity_constraint.py verifies these and injects non-equivariant and detuned counterexamples. MathCan/TOETensorConstraints.lean supplies conditional source compensation, minimal-rank, quadratic isotropy, and 2-by-2 little-group lemmas, subject to GitHub CI.

The machine-readable receipt records source_multiplet_pointwise_D_jets_realized=true and explicitly preserves the stronger open gates: source_multiplet_jet_integrability_verified=false, source_multiplet_background_equations_solved=false, complete_constrained_GfE_YM_tensor_system_derived=false and strong_hyperbolicity_verified=false.

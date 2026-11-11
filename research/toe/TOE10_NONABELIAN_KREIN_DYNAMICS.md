# TOE-10: Gauge-covariant SU(2)² bivector matter, Krein boundaries, and dynamical loss of real spectrum

**Status, 11 November 2026.** This MathCan investigation constructs a **candidate** non-Abelian gauge-invariant extension of the Abelian 2-form term in Ginestra Bianconi's *Gravity from Entropy* (2025), then derives exact necessary spectral conditions and an explicit finite-time crossing on a self-consistent **Einstein–Yang–Mills** background. We also define and vary a separate logarithmically coupled gauge-medium action on a prescribed FLRW spacetime. Those field equations incorporate a nonzero 2-form logarithmic backreaction on the gauge fields. The entire *coupled* metric/G-field/gauge system of Bianconi's ΛGfE theory has **not** been derived or solved. This is a mathematical hypothesis and testing architecture, not a result about observable gravitational waves.

## Sources and sharp boundary between source and new construction

* [Bianconi, *Gravity from entropy* (2025), arXiv:2408.14391](https://arxiv.org/html/2408.14391), Appendix A: the **Abelian** gauge-field 2-form tensor (field-strength outer product), Appendix B: the Lorentzian bivector metric and generalized operator. The paper explicitly leaves continuum non-Abelian inclusion for future investigation. The scalar, one-form, and bivector sectors coexist in its full operator.
* [Bianconi, *Λ-Gravity from Entropy* (2026), arXiv:2610.34496](https://arxiv.org/abs/2610.34496): constant volume multiplier and dynamical G-field, metric equations and dressed matter.
* [Pereira, *Gravitational Waves and Matter Constraints in Gravity from Entropy* (2026), arXiv:2609.03082](https://arxiv.org/abs/2609.03082): TT strict-principal tensor obstruction in vacuum and specified single-multiplet/perfect-fluid sectors. Its matter rank theorem motivates two multiplets without supplying their field equations.
* MathCan's [TOE-08C](TOE08_TWO_GAUGE_TRIADS.md) and [TOE-09](TOE09_LORENTZ_BIVECTOR_SPECTRUM.md) define, respectively, a Euclidean observer-frame Gram model and the Lorentzian generalized-eigenvalue gate. TOE-10 uses the **Lorentzian** convention; it does not replace the two models silently.

The extension below assigns a **Killing-form contracted** gauge-field tensor to the 2-form sector. The choice to use the same coupling `alpha` in this channel and the normalization `alpha=6 beta kappa` drawn from the scalar GfE limit are stated **hypotheses**. Different operator coefficients can change the numerical bound. SU(2) adjoint color triplets do not automatically equal two of Bianconi's fundamental Dirac–Kähler multiplets.

## 1. A gauge-invariant full six-dimensional constitutive map

Let \(I=1,2\) label independent SU(2) factors and \(a=1,2,3\) adjoint indices. Set

\[
F_{I\mu\nu}=\partial_\mu A_{I\nu}-\partial_\nu A_{I\mu}+g_I[A_{I\mu},A_{I\nu}],
\qquad
M_{\mu\nu,\rho\sigma}^{(2)}
 =\sum_{I=1}^2\delta_{ab}F^a_{I\mu\nu}F^b_{I\rho\sigma}.
\tag{1}
\]

For independent local gauge transformations \(U_I(x)\), each \(F_I\) transforms by conjugation and the positive Killing-form contraction \(\delta_{ab}F_I^a F_I^b\) is unchanged. This is a **gauge invariant, diffeomorphism covariant candidate matter tensor**. It is distinct from a flavor rotation, which need not be a gauge symmetry.

Define the mixed bivector operator on \(\Lambda^2 T^*M\) as

\[
\Theta_{(2)}=I+\alpha M_{(2)}g_{(2)}^{-1}-\beta\mathcal R_{(2)}.
\tag{2}
\]

The relative placement of the Lorentzian bivector inverse metric matters. In an orthonormal frame \((-+++)\), flatten the 2-forms in the order \((01,02,03,23,31,12)\) and write \(S=\operatorname{diag}(-I_3,I_3)\). The source model is *S-self-adjoint*, \(\Theta^\mathsf TS=S\Theta\), while its usual matrix representation may be nonsymmetric.

For the homogeneous isotropic triad \(A_{Ii}^a=a\psi_I\delta_i^a\), define

\[
E_I=\dot\psi_I+H\psi_I,\qquad B_I=g_I\psi_I^2,
\qquad e=\sum E_I^2,\quad b=\sum B_I^2,\quad c=\sum E_IB_I.
\tag{3}
\]

The covariant Gram matrix is \(\left(\begin{smallmatrix}eI_3&cI_3\\cI_3&bI_3\end{smallmatrix}\right)\). Raising the second bivector pair produces \(\left(\begin{smallmatrix}-eI_3&cI_3\\-cI_3&bI_3\end{smallmatrix}\right)\). In flat FLRW, where \(A=H^2+\dot H\) and \(B=H^2\), the three identical real blocks of Eq. (2) are

\[
\Theta_*=
\begin{pmatrix}\theta_E&\alpha c\\-\alpha c&\theta_B\end{pmatrix},
\quad
\theta_E=1-\alpha e-2\beta A,
\quad
\theta_B=1+\alpha b-2\beta B.
\tag{4}
\]

The Python oracle constructs all 36 entries **from independently rotated adjoint gauge frames** and checks that separate SO(3) rotations leave the tensor unchanged. This tests covariance of the proposed contraction, not uniqueness of a non-Abelian extension.

## 2. Positive-real eigenvalue gate and the missing normalization factor

The characteristic discriminant of one block is

\[
\boxed{\Delta=(\theta_E-\theta_B)^2-4\alpha^2c^2
=\left[-\alpha(e+b)-2\beta\dot H\right]^2-4\alpha^2c^2.}\tag{5}
\]

With \(D=\det\Theta_*=\theta_E\theta_B+\alpha^2c^2\), distinct positive real eigenvalues require \(\Delta>0\), \(\operatorname{tr}\Theta_*>0\), and \(D>0\). The case \(\Delta=0\) and \(c\ne0\) is a defective Jordan block. A *matrix* logarithm can exist at a positive defective eigenvalue, but the diagonal eigenbasis treatment and strict semisimplicity gate used in the code exclude that boundary. A complex-conjugate pair at \(\Delta<0\) falls outside Bianconi's positive-real eigenvalue premise.

For the separately specified *minimal Einstein–Yang–Mills* system,

\[
\rho_{\rm YM}=\tfrac32s,\quad p_{\rm YM}=\tfrac12s,
\quad s=e+b,
\quad \dot H=-\kappa s,
\quad 3H^2=\Lambda+\kappa\rho_{\rm YM}.
\tag{6}
\]

Consequently the diagonal gap is exactly

\[
\theta_E-\theta_B=(2\beta\kappa-\alpha)s.
\tag{7}
\]

**TOE-10/T1 (conditional normalization obstruction).** With \(\beta,\kappa>0\), \(s>0\), and **the declared scalar-GfE-inspired coupling choice** \(\alpha=6\beta\kappa\), the gap equals \(-4\beta\kappa s<0\). Thus the diagonal-electric/magnetic equality required by a *diagonal-only* cone-matching prescription never holds for a nontrivial YM radiation source. This is a restriction on the declared model and the GR laboratory; the full ΛGfE cosmological equations and the proper normalization of a new non-Abelian 2-form channel can change this conclusion.

Substituting Eq. (7) in Eq. (5) gives

\[
\boxed{\Delta=16\beta^2\kappa^2(s^2-9c^2),
\qquad |c/s|<1/3\ \text{for the strict real-split branch}.}\tag{8}
\]

Cauchy–Schwarz ensures \(|c|\le s/2\), so positive gauge energy does not by itself enforce this stricter gate. This condition is independent of the magnitude of the overall background energy, but other sectors and the eigenvalue trace/determinant still need to be checked.

## 3. Exact Yang–Mills flow and the expansion-free ratio

Minimal YM field equations for each triad are

\[
\dot\psi_I=E_I-H\psi_I,\qquad
\dot E_I=-2HE_I-2g_I^2\psi_I^3,
\qquad\dot B_I=2g_I\psi_I E_I-2HB_I.
\tag{9}
\]

They imply

\[
\dot s=-4Hs,\quad
\dot c=-4Hc+2\sum_Ig_I\psi_I(E_I^2-B_I^2).
\tag{10}
\]

**TOE-10/T2 (normalized flow).** Let \(r=c/s\) for \(s>0\). Then

\[
\boxed{\dot r=\frac{2\sum_I g_I\psi_I(E_I^2-B_I^2)}s.}\tag{11}
\]

This identity follows from exact cancellation of \(H\)-dilution in the quotient rule. It is tested on 120 seeded rational two-multiplet configurations. Lean formalizes its integer cross-multiplied transport numerator with the evolution hypotheses supplied explicitly.

## 4. A strict-interior state reaches the complex sector in finite time

Take \(g_1=g_2=1\), \(\kappa=1/10\), \(\beta=1/100\), \(\alpha=6\beta\kappa=3/500\), and an expanding flat background with \(H=1\). At the boundary set

\[
(\psi_1,E_1)=(1,2),\qquad(\psi_2,E_2)=(0,1).
\]

Then \(e=5\), \(b=1\), \(c=2\), \(s=6\), \(\dot H=-3/5\), \(\Lambda=21/10\), and

\[
\theta_E=481/500,\qquad\theta_B=493/500,
\quad\Delta=0,\qquad\boxed{\dot\Delta=-54/15625}.\tag{12}
\]

The nonzero mixed block at \(\Delta=0\) makes this **boundary state defective**. Perturb the second electric amplitude to \(E_2=100001/100000\). The state now has \(\Delta>0\), positive trace and determinant, so all six proposed 2-form eigenvalues are positive and real. A *single exact-rational RK4 step* of duration \(10^{-4}\) for the fully coupled **GR+YM** background gives \(\Delta<0\), with trace and determinant remaining positive. Two half-steps reproduce the sign and agree in the matter variables to the documented floating error tolerance. This supplies a concrete numerical counterexample to **automatic preservation** of the spectral gate in the GR+YM laboratory; the exact negative time derivative at the neighboring boundary gives its local analytic mechanism.

The fixture records exact initial rational data, a reproducible step and an explicit *synthetic* provenance flag. There is no observational fit or assertion that this trajectory satisfies ΛGfE.

## 5. A definite gauge-invariant logarithmic matter deformation

To test gauge-field feedback beyond minimal YM, define a **trial** action on a prescribed spacetime:

\[
S_{\rm trial}[A;g]=\int\sqrt{-g}
\left[-\frac14\sum_{I,a}F^a_{I\mu\nu}F_I^{a\mu\nu}
-\sigma\log\det\Theta_{(2)}\right]d^4x.
\tag{13}
\]

Here \(\sigma\ge0\) sets the logarithmic-medium strength. The full 2-form operator of this specific model is Eq. (2), so \(\log\det\Theta_{(2)}=3\log D\) whenever an admissible branch is chosen. Equation (13) is local and gauge invariant, with field strengths replacing any gauge-dependent potential Gram. It is **not identified with the complete Bianconi GQRE action**, which includes all form sectors, independent G-field and volume equations, and the metric's induced variation.

The homogeneous trial Lagrangian per physical volume is

\[
\mathcal L=\frac32\sum_I(E_I^2-B_I^2)-3\sigma\log D.
\]

Writing \(P_I=\partial\mathcal L/\partial E_I\) and \(Q_I=\partial\mathcal L/\partial B_I\), the explicit constitutive momenta are

\[
\boxed{
P_I=3E_I+\frac{6\sigma\alpha}{D}(\theta_BE_I-\alpha c B_I),\qquad
Q_I=-3B_I-\frac{6\sigma\alpha}{D}(\theta_EB_I+\alpha cE_I).}
\tag{14}
\]

Varying \(A_i^a=a\psi\delta_i^a\) before fixing the gauge-field trajectory gives

\[
\boxed{\dot P_I+2H P_I-2g_I\psi_IQ_I=0.}\tag{15}
\]

This is the homogeneous reduction of a gauge-covariant constitutive equation schematically \(D^{(I)}_\mu\mathcal H_I^{a\mu\nu}=0\), where \(\mathcal H\) is obtained by differentiating the specified action with respect to \(F^a_{\mu\nu}\). The Python solver differentiates Eq. (14) analytically, including curvature-jet response, and solves the full two-by-two Legendre matrix for \(\dot E_I\) on a supplied \((H,\dot H,\ddot H)\) background.

**TOE-10/T3 (local matter closure).** If the induced block is on the positive-real semisimple branch and \(\det[\partial P_I/\partial E_J]\ne0\), then Eq. (15) uniquely fixes the two electric accelerations for a specified metric jet. At \(\sigma=0\), the system reduces exactly to both minimal Yang–Mills equations. For the rational initial state of section 4 and \(\sigma=1/100\), the Legendre determinant is positive and the exact discriminant derivative remains negative. The latter is a **local** source-response result on an externally supplied metric jet; the metric would need to be re-solved for a coupled ΛGfE trajectory.

The matrix logarithm is well-defined beyond the spectral domain as an analytic continuation in some regions. Our checker is deliberately strict: it refuses to evolve an unacceptable positive-real branch, including defective boundary points, to avoid treating continuation as a physical GQRE state. For derivative tests alone, the underlying rational functions can be inspected on that continuation, with the branch check explicitly bypassed.

## 6. Tests, formalization, and remaining full-theory gates

`nonabelian_gfe.py` implements exact gauge-frame invariance, Lorentzian six-dimensional response reconstruction, the Krein discriminant, GR+YM lapse/continuity constraints, rational short-time stepping, and a nonzero-\(\sigma\) constitutive Euler solver. `tests/test_toe10_nonabelian.py` tests the strict-interior Krein crossing, color-frame rotations, exact transport identities, Legendre Hessian symmetry, independent numerical difference quotients, sigma-zero YM recovery, and the local sigma-positive discriminant sign. The optional `derive_nonabelian_sympy.py` independently reconstructs momenta and Hessian from Eq. (13). The Lean module `MathCan/TOENonAbelian.lean` proves only the algebraic response-budget/transport consequences under stated integer hypotheses and displays its axiom audit.

**Open:** derive the complete non-Abelian Dirac–Kähler induced operator and settle its relative channel coefficients; include the G-field and constant-Λ constraints, curvature-connection response and dressed stress-energy; solve the coupled background and gauge equations; linearize metric, G-field, gauge and constraints together; obtain the full principal determinant and a strong-hyperbolicity symmetrizer; identify a physical frequency cutoff. A matched diagonal block is insufficient to certify real gravitational-wave propagation in the fully coupled system.

### Reproduce

```sh
python -m unittest tests.test_toe10_nonabelian -v
python -m research.toe.nonabelian_gfe
python research/toe/derive_nonabelian_sympy.py  # optional: SymPy
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/TOENonAbelian.lean
```

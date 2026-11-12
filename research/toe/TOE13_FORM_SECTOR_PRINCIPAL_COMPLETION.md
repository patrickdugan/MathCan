# TOE-13: The 0/1-form curvature completion lifts the TOE-12 Jordan root

**November 12, 2026.** The calculation adds the missing scalar-curvature and Ricci-tensor form sectors of Bianconi's 0/1/2-form construction to MathCan's declared TOE-11/12 2-form plus two-SU(2)-Yang–Mills **frozen-background trial model**. It constructs the scalar/vector fourth-order TT principal bilinear from the source's form-sector structure, independently verifies the full 4×4 Ricci perturbation and determinant, and checks algebraic elimination of an auxiliary G-field. The old six-mode repeated characteristic is **lifted** in this form-sector completion. The reference two-mode formal polynomial has one real root and a nonreal conjugate pair of squared-frequency roots. The calculation neither supplies a complete physical GfE action with this non-Abelian matter choice nor eliminates the metric, gauge and G-field constraints.

## Source attribution and precise assumptions

* G. Bianconi, [*Gravity from Entropy*, Phys. Rev. D 111, 066001 (2025)](https://doi.org/10.1103/PhysRevD.111.066001), [arXiv 2408.14391 HTML](https://arxiv.org/html/2408.14391). Sections III.1–III.3 introduce the direct sum of 0-, 1-, and 2-form metrics, with scalar curvature R, Ricci R^mu_nu, and Riemann acting on their respective sectors. Section III.5 introduces an independent auxiliary G-field and its algebraic inverse relation. Published errata are relevant when using source component expressions.
* G. Bianconi, [*Λ-Gravity from Entropy* (2026)](https://arxiv.org/abs/2610.34496) includes a local-volume multiplier and revised metric/G-field equations; the multiplier does not enter the **fourth-order metric principal of the algebraically eliminated curvature-log sector** analyzed here.
* MathCan [TOE-11](TOE11_COUPLED_PRINCIPAL_SCHUR.md) constructed a **declared** non-Abelian two-SU(2) gauge/2-form logarithmic action, with a 6×6 bivector curvature response. [TOE-12](TOE12_TENSOR_JORDAN_GAUGE_CONSTRAINTS.md) isolated the corresponding two-helicity plus four-gauge-mode tensor symbol and proved a repeated-root defect. Neither module contained the source's 0/1-form **metric** curvature blocks in its frozen principal operator.

The completion in this note is the **block-diagonal, curvature-only** ansatz

\[
\mathcal L_{\mathrm{form}}=-\sigma_0\log\theta_0
-\sigma_1\log\det\Theta_{(1)},\qquad
\theta_0=1-\beta R,\quad
\Theta_{(1)}=I_4-\beta R^\mu{}_{\nu}.
\tag{1}
\]

The reference sets sigma_0=sigma_1=sigma_2=1/100 for a transparent same-strength comparison. These strengths are normalization parameters of the **trial completion**. The exact complete GfE normalization and the 0/1-form matter content require separate source-specific matching. In this calculation we use a flat FLRW curvature background with A=H²+Hdot and B=H², and a local orthonormal frame with signature (-,+,+,+):

\[
\theta_0=1-6\beta(A+B),\quad
\Theta_{(1)}=\operatorname{diag}(\theta_t,\theta_s,\theta_s,\theta_s),\quad
\theta_t=1-3\beta A,\quad\theta_s=1-\beta(A+2B).
\tag{2}
\]

An additional homogeneous temporal matter shift to theta_t can be supplied as a parameter; it does not affect the TT-spatial result **when matter perturbations are held fixed**. For the reference A=2/5, B=1, beta=1/100, the exact denominators are (229/250,247/250,122/125), all positive.

## T1. Scalar TT null and positive vector Ricci-log correction

Let h_{11}=+1,h_{22}=-1 denote the plus transverse-traceless metric polarization, or h_{12}=h_{21}=+1 denote cross. At local covector xi=(omega,0,0,p), the standard flat-frame Ricci principal tensor is

\[
\delta R_{\mu\nu}(\xi,h)=\frac12\Big[\xi_\mu\xi_\alpha h^\alpha{}_{\nu}+\xi_\nu\xi_\alpha h^\alpha{}_{\mu}-\xi_\mu\xi_\nu h-\xi^2 h_{\mu\nu}\Big].
\tag{3}
\]

For either TT polarization, xi^mu h_{mu nu}=h=0, whence delta R=0. The only nonzero delta Ricci components are transverse spatial components and are proportional to (omega²-p²)/2 times h. Therefore the scalar block's fourth-order contribution vanishes on this TT subspace.

The Hessian of the negative vector log determinant is

\[
\delta^2(-\sigma_1\log\det\Theta_1)
=\sigma_1\beta^2\operatorname{tr}
\big(\Theta_1^{-1}\delta R^{(1)}\Theta_1^{-1}\delta R^{(1)}\big)
\,+\text{lower-derivative curvature/metric terms}.
\tag{4}
\]

Directly evaluating the two TT polarizations gives

\[
\boxed{\delta^2\mathcal L_{\rm form}|_{\rm TT}
=\frac{\sigma_1\beta^2}{2\theta_s^2}
(\omega^2-p^2)^2(h_+^2+h_\times^2),}
\quad C_1:=\frac{\sigma_1\beta^2}{2\theta_s^2}.
\tag{5}
\]

For the reference beta=1/100, theta_s=122/125, sigma1=1/100:

\[
\boxed{C_1=1/1{,}905{,}152.}
\]

This is checked two independent ways: exact contraction of all 16 Ricci components through the 4×4 inverse response, and determinant evaluation of a perturbed 4×4 Theta_1 (100 seeded rational cases). The latter has ratio `det Theta_1(epsilon) / det Theta_1(0) = 1 - epsilon² [beta(omega²-p²)/(2theta_s)]²` for an isolated normalized TT polarization. Pure-gauge metric amplitudes delta h_mu_nu = xi_mu v_nu + xi_nu v_mu have identically zero delta Ricci and pass 125 rational cases. We also check the exact linearized contracted Bianchi identity.

## T2. The former repeated characteristic is now an invertible tensor matrix

Write r=theta_E/theta_B for the prior 2-form trial block and denote the four-gauge-mode subblock by G(omega). TOE-12 proved the exact two-helicity factorization

\[
P_{12}(\omega)=\begin{pmatrix}
(\omega^2-r)^2A&(\omega^2-r)B(\omega)\\
(\omega^2-r)B(\omega)^T&G(\omega)
\end{pmatrix},\quad
\det G(\sqrt r)\neq0.
\]

In the current completion Eq. (5) adds `C1(omega²-p²)² I2` to the metric block, with no direct fourth-order 0/1-form gauge-field mixing (the latter is held fixed by hypothesis). Use p=1. Then *at the former root* omega²=r the old metric and mixed blocks vanish, and

\[
\boxed{
\det P_{13}(\sqrt r)=
[C_1(r-1)^2]^2\det G(\sqrt r)\ne0.
}\tag{6}
\]

At the pinned TOE-11/12 background:

\[
\boxed{r=\frac{480993997}{493000000},\qquad r\ne1.}
\]

The exact determinant calculation takes place in Q(sqrt(r)), using the original independently tested TOE-12 polynomial coefficients; a second exact six-by-six determinant computation validates Eq. (6). The determinant is positive and is approximately 5.4514385e-25 in the dimensionless formal normalization. **TOE-12's Jordan root is removed at its old frequency in this completed restricted model.** That is the justified claim: the full spectrum and characteristic Jordan structure at every other root remain to be examined.

## T3. The restricted two-mode polynomial acquires a complex pair

For one TT and one gauge tensor polarization, let the original formal symbol be

\[
P_{11}(\omega)=a_4\omega^4+a_2\omega^2+a_0,\quad
P_{12}(\omega)=m_3\omega^3+m_1\omega,\quad
P_{22}(\omega)=g_2\omega^2+g_0.
\]

With x=omega²/p² and p=1, the added 1-form sector changes the determinant polynomial by

\[
\boxed{d_{13}(x)=d_{12}(x)+C_1(x-1)^2(g_0+g_2x).}\tag{7}
\]

An **exact rational cubic discriminant calculation** for C1=1/1905152 finds a negative discriminant: there is exactly one real x root and two nonreal conjugates. The unique real root lies in (0,1), using the exact polynomial signs there. The negative discriminant persists in the tested strengths sigma1=1/100, 1/10000 and 1/1000000. Numerical roots at sigma1=1/100 are approximately

* x_real = 0.999999202003714;
* x_pair = 0.980406513972802 ± 0.009656076250606 i.

These are roots of the **formal TOE-11 symmetric symbol polynomial**, whose odd-frequency mixed entries require consistent Fourier i factors and an actual constrained first-order reduction before one can call them physical dispersion modes. Eq. (7) is a structural alert about the omitted 1-form sector, not a measurement of a propagating instability.

## T4. An independent auxiliary G-field Schur identity

The logarithmic curvature formulation has an exact algebraic first-order representation. For an invertible positive-background matrix Theta, choose the auxiliary functional

\[
L(G,\Theta)=-\operatorname{tr}(G\Theta)+\log\det G+n,
\]

whose stationary equation is `G=Theta^{-1}` and whose on-shell value is `-log det Theta`. If a curvature perturbation produces D=delta Theta, stationarity at first order gives

\[
\boxed{\delta G=-\Theta^{-1}D\Theta^{-1}.}\tag{8}
\]

At a stationary background, the Hessian of the unreduced functional in the two perturbations (D,K=delta G) is

\[
H((D,K),(D',K'))=-\mathrm{tr}(KD'+K'D)
-\mathrm{tr}(\Theta K\Theta K').
\]

Eliminating K,K' by Eq. (8) gives the exact Schur complement

\[
\boxed{H_{\mathrm{eff}}(D,D')
=\operatorname{tr}(\Theta^{-1}D\Theta^{-1}D').}\tag{9}
\]

The `auxiliary_g_schur.py` oracle independently evaluates both sides over 160 seeded rational diagonal-background 4×4 matrix configurations, with arbitrary (possibly nonsymmetric) perturbations, and checks the direct TT 1-form value. This establishes equivalence **for the algebraic G sector at fixed metric/gauge curvature jets**. The independent G field changes the differential order of the unreduced coupled system; full G constraints, other form channels and lapse/shift variables are still needed for its physical characteristic matrix.

## Results, labels and reproducibility

* **SOURCE-BASED SECTOR STRUCTURE:** GfE's 0/1/2 curvature blocks and algebraic G-field inverse come from Bianconi's published construction.
* **PROVED, CONDITIONAL:** T1–T4 for the explicitly defined frozen-background curvature-log completion; their algebra is given above.
* **EXACT EXECUTABLE:** 28 TOE-13 Python tests, a Q(sqrt(r)) six-mode determinant, a cubic discriminant, contracted-Bianchi and metric-gauge-null controls, independent 4×4 determinant tests, and the matrix G-Schur identity. The reference uses synthetic values.
* **LEAN-CHECKED SUBSET:** `MathCan/TOEFormSectors.lean` formalizes finite integer TT trace, nonzero lifted determinants and two-helicity kernel consequences after Lean CI.
* **OPEN:** the full non-Abelian matter coupling in the 0/1-form sectors, source-normalized graviton/gauge GfE action, all lapse/shift and YM Gauss constraints, full independent-G spacetime characteristic matrix, field background equations, finite-frequency physical propagation and strong hyperbolicity.

```
python -m unittest tests.test_toe13_form_sectors tests.test_toe13_gfield_schur -v
python -m research.toe.form_sector_principal
python -m research.toe.auxiliary_g_schur
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/TOEFormSectors.lean
```

# TOE-05: Coupled scalar–geometry dynamics in a homogeneous Lambda-GfE reduction

**Status, 11 November 2026:** primary-source action reduced to a spatially flat, expanding FLRW metric and a **real homogeneous scalar field**; algebraic G-field constraint eliminated; lapse and scalar Euler–Lagrange equations derived at the reduced-action level; coupled acceleration system solved; positive Schur determinant proved by an exact algebraic decomposition and checked with rational arithmetic; numerical branch tested. **The full covariant metric equation with its dressed stress tensor and derivative tensor has not yet been verified component by component.** The integration is synthetic. None of the numbers below is a cosmological fit or a prediction of the full theory's physical viability.

## Primary sources and attribution

* G. Bianconi, [*Lambda-Gravity from Entropy*, arXiv:2610.34496](https://arxiv.org/abs/2610.34496) (2026), especially Eqs. **(5)** (induced metric), **(7)** (matter 0- and 1-form tensors for a scalar), **(9)** (logarithmic GQRE action), **(16)** (inverse G-field), **(19)** (emergent Lambda), **(31)** (constrained volume), and **(45)–(49)** (dressed metric, trace-free and joint conservation equations).
* G. Bianconi, [*Thermodynamics of the Gravity from Entropy Theory*, arXiv:2510.22545](https://arxiv.org/abs/2510.22545) (revised 2026), homogeneous isotropic spectral sectors and their flattened degeneracies.
* [TOE-04 MathCan](BIANCONI_FLRW_GFIELD_DYNAMICS.md), the **vacuum** case to which the scalar system must reduce.

Our FLRW lapse calculation, closure theorem, exchange diagnostic and numerical solver are MathCan derivations from the cited action. The field equations and their physical interpretation belong to Bianconi. We make no novelty claim for standard minisuperspace variational techniques or the Schur complement.

## 1. The five positive induced-metric sectors

Use signature `(-,+,+,+)`, lapse `N(t)`, scale factor `a(t)`, curvature `k=0`, and a real homogeneous scalar `phi(t)` of mass `m>=0`. Put

\[
H=\frac{\dot a}{Na},\quad D=\frac{\dot H}{N},\quad
\pi=\frac{\dot\phi}{N},\quad A=H^2+D,\quad B=H^2.
\]

The source selects `M_(0)=m^2 phi^2`, `M_(1),mu nu=partial_mu phi partial_nu phi`, and `M_(2)=0`. The time vector component has **negative** raised sign because `g^00<0`. With the source's `G_tilde=I+alpha*M-beta*R`, the spectral eigenvalues of `Theta=G_tilde*g_tilde^{-1}` are

| Component | Multiplicity | theta = 1 + alpha M - beta R |
| --- | ---: | --- |
| scalar | 1 | `d0=1+alpha*m^2*phi^2-6*beta*(A+B)` |
| time vector | 1 | `d1=1-alpha*pi^2-3*beta*A` |
| spatial vector | 3 | `d2=1-beta*(A+2*B)` |
| time–space bivector | 3 | `d3=1-2*beta*A` |
| spatial bivector | 3 | `d4=1-2*beta*B` |

The G-field eigenvalues are `G_i=1/d_i`; every `d_i` must be **strictly positive**. A zero eigenvalue ends the integration. Under these assumptions the on-shell geometric quantum relative entropy density is

\[
 f(A,B,\phi,\pi)
 =-\ln d_0-\ln d_1-3\ln d_2-3\ln d_3-3\ln d_4.
 \tag{1}
\]

The scalar's contribution cannot be reduced to the vacuum curvature-only eigenvalues by simply adding a conventional fluid energy density to `H²`. It changes the *G-field* itself, including its curvature derivatives.

## 2. Vary the volume multiplier in the correct order

The `Lambda` volume-constraint term is `L_Lambda=(6 beta Lambda/omega)(omega-sqrt(-g))`. Vary the independent metric at fixed auxiliary `omega`, **then** impose `omega=sqrt(-g)`. As in TOE-04, this contributes an effective `-6 beta Lambda` to the metric variation. The metric-equation equivalent reduced functional is

\[
 S_{\rm red}\propto \int dt\,Na^3\left[f(A,B,\phi,\pi)-6\beta\Lambda\right].
 \tag{2}
\]

The scalar action's exact variation is unchanged by that auxiliary term. In this module `Lambda` is a constant to be fixed by initial data and joint Noether compatibility; treating it as an independently prescribed redshift function would violate the source's on-shell equation (49).

### The scalar equation

Write `f_pi=partial f/partial pi` and similarly for `phi`. Then

\[
 f_\pi=\frac{2\alpha\pi}{d_1},\qquad
 f_\phi=-\frac{2\alpha m^2\phi}{d_0}.
\]

Euler–Lagrange variation of `phi` in Eq.(2) yields

\[
 \frac{d}{dt}\left(\frac{\pi}{d_1}\right)
 +3H\frac{\pi}{d_1}+\frac{m^2\phi}{d_0}=0.
 \tag{3}
\]

For `d0,d1 -> 1` it becomes the ordinary homogeneous Klein–Gordon equation `dot(pi)+3H*pi+m²*phi=0`. Equation (3) is the dynamical matter equation of the stated symmetry-reduced scalar action; it is **not** a separately assumed conservation law for the full dressed stress-energy tensor.

### The lapse constraint

At `N=1`, a change of lapse has `delta H=-H delta N`, `delta D=-2D delta N-H delta(dot N)`, `delta pi=-pi delta N` and `delta A=-2A delta N-H delta(dot N)`. Varying Eq.(2) and integrating the `delta(dot N)` term by parts gives

\[
\boxed{0=f-6\beta\Lambda+(H^2-D)f_A-2H^2f_B
      -\pi f_\pi+H\frac{d f_A}{dt}.}
\tag{4}
\]

The scalar kinetic term `-pi*f_pi` is essential. Dropping it gives the wrong GR limit and does not conserve the chosen reduced variational system. The derivatives needed below are

\[
\begin{aligned}
f_A&=\frac{6\beta}{d_0}+\frac{3\beta}{d_1}+\frac{3\beta}{d_2}+\frac{6\beta}{d_3},\\
f_B&=\frac{6\beta}{d_0}+\frac{6\beta}{d_2}+\frac{6\beta}{d_4},\\
f_{AA}&=\frac{36\beta^2}{d_0^2}+\frac{9\beta^2}{d_1^2}
+\frac{3\beta^2}{d_2^2}+\frac{12\beta^2}{d_3^2},\\
f_{AB}&=\frac{36\beta^2}{d_0^2}+\frac{6\beta^2}{d_2^2},\\
f_{A\pi}&=\frac{6\alpha\beta\pi}{d_1^2},\qquad
f_{A\phi}=-\frac{12\alpha\beta m^2\phi}{d_0^2},\\
f_{\pi\pi}&=\frac{2\alpha}{d_1}
+\frac{4\alpha^2\pi^2}{d_1^2}.
\end{aligned}\tag{5}
\]

## 3. Coupled acceleration and a strictly positive Schur determinant

Let `J=ddot H` and `P=ddot phi=dot pi` at lapse one, and note

\[
\dot A=J+2HD,\qquad\dot B=2HD.
\]

Eqs.(3)–(4) form the **linear** system

\[
\begin{pmatrix}
Hf_{AA}&Hf_{A\pi}\\
f_{A\pi}&f_{\pi\pi}
\end{pmatrix}
\binom{J}{P}
=-\binom{C_1}{C_2},\tag{6}
\]

with

\[
\begin{aligned}
C_1&=f-6\beta\Lambda+(H^2-D)f_A-2H^2f_B-\pi f_\pi
 +H\{2HD(f_{AA}+f_{AB})+f_{A\phi}\pi\},\\
C_2&=2HD f_{A\pi}+3H f_\pi-f_\phi.
\end{aligned}\tag{7}
\]

**TOE-05/T1 (local acceleration closure).** On `H>0`, `alpha,beta>0` and `d_i>0`, the determinant of the matrix in Eq.(6) is strictly positive. Indeed

\[
\begin{aligned}
\Delta/H&=f_{AA}f_{\pi\pi}-f_{A\pi}^2\\
&=\frac{2\alpha}{d_1}f_{AA}
+\frac{4\alpha^2\pi^2}{d_1^2}
  \left(f_{AA}-\frac{9\beta^2}{d_1^2}\right)>0.
\end{aligned}\tag{8}
\]

Both terms are nonnegative, and the first is strictly positive; the term in parentheses contains the positive scalar, spatial-vector, and time-bivector contributions. This gives unique real finite accelerations `J,P` for each admissible instantaneous state. It is a **local statement about the reduced ODE**. It provides no global-in-time regularity, perturbative stability, or ghost exclusion. The identity is checked exactly over the rationals in `rational_determinant`.

## 4. Correct weak-field limit and a matter-exchange diagnostic

With `alpha=6 kappa beta`, the first-order action is

\[
 f=18\beta(A+B)+\alpha(\pi^2-m^2\phi^2)+O(\beta^2),
\]

for fixed bounded fields. Dividing Eq.(4) by `6 beta` gives

\[
3H^2=\Lambda+\kappa(\pi^2+m^2\phi^2)+O(\beta).
\tag{9}
\]

Equation (3) independently tends to the Klein–Gordon equation. Both limits are checked by numerical finite-parameter tests, and setting `phi=pi=0` reduces *exactly* to the TOE-04 vacuum solver.

Define the **bare scalar diagnostic** `rho_b=pi²+m² phi²`, `p_b=pi²-m² phi²`. Directly from Eq.(3),

\[
\boxed{\dot\rho_b+3H(\rho_b+p_b)
=2\pi\left[\pi\frac{\dot d_1}{d_1}
+m^2\phi\left(1-\frac{d_1}{d_0}\right)\right].}
\tag{10}
\]

This is a precise diagnostic of the scalar's departure from *bare* GR continuity. The full GfE dressed stress tensor is defined by functional metric variation (source Eq.(26)), contains G-field dependence, and is subject to the joint tensor conservation identity (source Eq.(48)). Therefore Eq.(10) must **not** be called the conservation law for the full dressed tensor.

## 5. Full source trace-free and joint conservation gates

From the full covariant source, set `X_mu nu=R^G_(mu nu)+D_(mu nu)`. With isotropy `X_00=X0`, `X_ij=a² Xs δ_ij` and the *dressed* matter tensor `T_00=rho_G`, `T_ij=a² p_G δ_ij`, source Eq.(47) gives

\[
\boxed{X_0+X_s=3\kappa(\rho_{\mathcal G}+p_{\mathcal G}).}
\tag{11}
\]

A vacuum shift `rho_G -> rho_G+v`, `p_G -> p_G-v` leaves this equation invariant. The joint conservation law Eq.(48) takes the isotropic form, writing `F=R_G-6 Lambda_G`,

\[
\dot X_0+3H(X_0+X_s)+\frac12\dot F
=3\kappa\big[\dot\rho_{\mathcal G}
+3H(\rho_{\mathcal G}+p_{\mathcal G})\big].
\tag{12}
\]

Eqs.(11)–(12) and the trace constraint imply `dot Lambda=0`. The integer-level tensor projection and algebraic Noether consequence are formalized in `MathCan/TOEDressedMatter.lean`.

**The remaining covariant refinement gate** is to evaluate `R^G_(mu nu)`, `D_(mu nu)` (including their G-field derivatives), and the *metric variation* of the dressed scalar action along the numerical trajectory, and check Eqs.(45)–(48) at every sampled point. Until this is done, the scalar/metric minisuperspace ODE is a conditional candidate reduction, and the numerical curve cannot be presented as a fully verified ΛGfE solution.

## 6. Synthetic expanding solution

Use dimensionless units `H*=1` with `beta H*²=0.01`, `alpha=0.06`, `m/H*=0.4`, `kappa=1`. Set `H(0)=1`, `D(0)=-0.01`, `phi(0)=0.2`, `pi(0)=-0.1`. Choose the initial H jerk from the leading GR scalar equation, then determine `Lambda=2.978590919530843` from the **full nonlinear lapse and scalar constraints** at the initial state. This is a consistency initial-data construction, **not** a measurement of a physical cosmological constant.

| z | H/H* | phi | bare continuity residual |
| ---: | ---: | ---: | ---: |
| 0.0 | 1.000000 | 0.200000 | 0.000689 |
| 0.1 | 1.001233 | 0.210846 | 0.001009 |
| 0.2 | 1.003008 | 0.223495 | 0.001531 |
| 0.3 | 1.005481 | 0.238102 | 0.002433 |
| 0.4 | 1.008880 | 0.254810 | 0.004049 |
| 0.5 | 1.013509 | 0.273745 | 0.007005 |

The five G-field eigenvalues stay positive on this short interval. An RK4 step-halving test reproduces H and phi to eight decimal places, while both equations' algebraic residuals are below `1e-12` along the computed trajectory. Those residuals verify consistency with the **equations used in the numerical integrator**; their smallness alone does not establish the full covariant field equations.

The JSON fixture records the trajectory, dimensions and provenance. The standard-library implementation also checks the exact rational Schur determinant on 300 reproducible states, first and second derivatives by finite differences, vacuum regression, field-sign symmetry, invalid domains, and the scalar exchange identity.

## Reproduce

```sh
python -m unittest tests.test_toe05_dressed_scalar -v
python -m research.toe.gfield_scalar_flrw
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/TOEDressedMatter.lean
```

**Next challenge:** a componentwise covariant audit and a physical scalar choice with specified Cauchy data and stability. That is also the prerequisite to applying TOE-03's correlated-covariance profile to a source-verified matter-coupled H(z).

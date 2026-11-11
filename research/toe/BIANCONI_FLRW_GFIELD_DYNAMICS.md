# TOE-04: a vacuum ΛGfE FLRW reduction with positive G-field eigenvalues

**Date:** 2026-11-11. **Status:** source-based isotropic curvature decomposition; vacuum metric-only reduced action; lapse equation with a written variational proof; reproducible synthetic `H(z)` trajectories and exact-rational covariance profiling; nine Lean algebraic lemmas intended for GitHub kernel CI. **The dressed fluid equations, general curved-space or anisotropic equations, and any fit to measured cosmology remain outside this module.**

## Papers and what they establish

1. [Bianconi, *Λ-Gravity from Entropy*, arXiv:2610.34496](https://arxiv.org/abs/2610.34496), equations (5), (9), (16), (19), (31), (45)–(49): induced metric `I+αM−βR`, inverse G-field, emergent `Λ_G`, constrained-volume Lagrange multiplier `Λ`, full trace-free equations and conservation law.
2. [Bianconi, *The Thermodynamics of the Gravity from Entropy Theory*, arXiv:2510.22545](https://arxiv.org/abs/2510.22545), section III.1 and equations (28)–(37): five isotropic eigenvalues and multiplicities `1,1,3,3,3`, and G-field energy.
3. [Pereira, *Vacuum gravity from entropy: Stability, spectra, and exact waves*, Phys. Rev. D 114, 104029 (2026)](https://doi.org/10.1103/lxlj-ppwh): independently identifies the curvature-squared coefficients in the vacuum metric-only expansion, including an opposite-residue tachyonic spin-2 pole for positive beta in the quadratic spectrum. This reduction does not establish dynamical stability.
4. [TOE-03: Bianconi covariance-aware background profile](BIANCONI_GFIELD_PROFILE.md): declared synthetic redshifts and covariance, reused here solely as an identification test.

**Attribution:** the gravitational action and algebraic G constraint come from Bianconi. The following lapse reduction, explicit acceleration formula, and test integration are MathCan derivations. The source paper itself leaves full quantitative cosmological solutions to future work.

## 1. Five curvature sectors of FLRW

Use signature `(-,+,+,+)` and an FLRW metric with lapse `N(t)` and scale factor `a(t)`. Define

\[
 A=\frac{1}{N^2}\left(\frac{\ddot a}{a}-\frac{\dot a\dot N}{aN}\right),\qquad
 B=\frac{1}{a^2}\left(\frac{\dot a^2}{N^2}+k\right).
\]

At `N=1`, `A=\dot H+H²` and `B=H²+k/a²`. The scalar curvature is `R=6(A+B)`. The Ricci endomorphism has eigenvalues `3A` (once) and `A+2B` (three times). The bivector curvature operator, normalized relative to `g_(2)`, has eigenvalues `2A` (three) and `2B` (three). These agree with Bianconi's flattened sector conventions.

For **vacuum** `M=0`, the five `U=β R` eigenvalues, degeneracies and inverse G values are:

| k | Sector | u_k | multiplicity | G_k |
|---|---|---|---|---|
| 0 | scalar | `6β(A+B)` | 1 | `1/(1-u_0)` |
| 1 | timelike vector | `3β A` | 1 | `1/(1-u_1)` |
| 2 | spatial vectors | `β(A+2B)` | 3 | `1/(1-u_2)` |
| 3 | timelike bivectors | `2β A` | 3 | `1/(1-u_3)` |
| 4 | spatial bivectors | `2β B` | 3 | `1/(1-u_4)` |

The strictly positive induced metric domain requires `1-u_k>0` for all five sectors. Inside it each `G_k>0` and

\[
 \Lambda_{\mathcal G}=\frac{1}{6\beta}\sum_{k=0}^4
  z_k(\mathcal G_k-1-\ln\mathcal G_k)\ge0 \quad(\beta>0).
\]

For the perfect-fluid matter *algebraic diagnostic*, section IV of the thermodynamics paper gives `M_(0)=M_(2)=0` and
`M^0_0=-(3+5w)ρ/8`, `M^i_i=(1-w)ρ/8` for `d=4`. Thus `u_1` gains `α ρ(3+5w)/8` and `u_2` loses `α ρ(1-w)/8`. This is implemented in `fluid_eigenvalues`. The fluid's stress-energy variation, equation of state and energy exchange with the G-field must be enforced before it can serve as a physical cosmology.

## 2. The vacuum metric-only action and its quadratic check

The source eigenvalue constraint `G=(I−U)^{-1}` gives the reduced vacuum geometric Lagrangian

\[
 f(A,B)=-\sum_{k=0}^4 z_k\ln(1-u_k(A,B)). \tag{1}
\]

**Order of operations for Λ.** Bianconi introduces `\mathcal L_Λ=(6βΛ/ω)(ω−s)` where `s=√{-g}`. The term vanishes at the constraint `ω=s`, yet its contribution to the first metric variation is nonzero: varying `s` with `ω` held fixed gives

\[
 \delta_s\big[s\mathcal L_Λ\big]_{\omega=s}=-6\beta\Lambda\,\delta s.
\]

For deriving the *vacuum metric equation*, this acts like the constant density `−6βΛs`. Consequently the minisuperspace metric equations follow by varying

\[
 S_{\rm vac}\;\propto\;\int dt\,N a^3\{f(A,B)-6\beta\Lambda\}. \tag{2}
\]

This expression is a **metric-equation equivalent reduction** after the auxiliary constraint's variation. Simply substituting `ω=s` in the original auxiliary action before variation would lose the Λ term.

Expanding the logarithms to second order gives

\[
 f(A,B)=3\beta R+\frac{\beta^2}{2}
 \left[R^2+R_{\mu\nu}R^{\mu\nu}+R_{\mu\nu\rho\sigma}R^{\mu\nu\rho\sigma}\right]+O(\beta^3\mathcal R^3).
\]

The exact FLRW polynomial inside the square brackets is

\[
 60A^2+84AB+60B^2
 = 5R_{\mu\nu}R^{\mu\nu}+\mathsf{GB},\qquad
 \mathsf{GB}=24AB. \tag{3}
\]

This reproduces the `3βR` and `5β²/2 Ricci²` coefficients identified by Pereira, modulo the Gauss–Bonnet topological term. `MathCan/TOEFLRW.lean` checks the 11-component flattened trace, curvature coefficients, and identity (3) over arbitrary integer monomials. The logarithmic identities and differential equations here are **written proofs with numerical checks**, outside the current Lean kernel coverage.

## 3. Positive Hessian and an acceleration equation

Let `d_k=1−β(c_{Ak}A+c_{Bk}B)` with rows `[(6,6,1),(3,0,1),(1,2,3),(2,0,3),(0,2,3)]`. Here the last component is the multiplicity. Then

\[
 f_A=\sum_k\frac{z_k\beta c_{Ak}}{d_k},\quad
 f_B=\sum_k\frac{z_k\beta c_{Bk}}{d_k},\quad
 f_{XY}=\sum_k\frac{z_k\beta^2 c_{Xk}c_{Yk}}{d_k^2}.
\]

For any `(v_A,v_B)` its Hessian quadratic form is

\[
 v^\top\nabla^2 f\,v=\sum_k z_k
 \left[\frac{\beta(c_{Ak}v_A+c_{Bk}v_B)}{d_k}\right]^2.\tag{4}
\]

The sector vectors `(3,0)` and `(0,2)` span the two-dimensional curvature plane. With `β>0` and all `d_k>0`, expression (4) is strictly positive for every nonzero `v`; `f_{AA}>0` follows in particular.

Varying the *lapse* in equation (2), then setting `N=1`, gives the Hamiltonian constraint for spatial flatness,

\[
 0=f-6\beta\Lambda+(H^2-\dot H)f_A
      -2H^2 f_B+H\dot f_A, \tag{5}
\]

where `\dot f_A=f_{AA}(\ddot H+2H\dot H)+2H\dot H f_{AB}`. This formula follows from
`∂L/∂N−d(∂L/∂\dot N)/dt=0`; the `\dot N` term in `A` is essential. Equation (5) is **affine in** `\ddot H`. For expanding `H>0`, strict positivity of `f_{AA}` yields the unique value

\[
 \boxed{\ddot H=\frac{6\beta\Lambda-f-(H^2-\dot H)f_A
                     +2H^2f_B-2H^2\dot H(f_{AA}+f_{AB})}
                    {Hf_{AA}}}. \tag{6}
\]

The spatial metric equation is related to the Hamiltonian constraint by time-reparametrization invariance on an expanding branch. This model integrates (6) with `\dot z=−(1+z)H`. We restrict to spatial flatness and positive H, and stop when any G eigenvalue loses positivity. The algorithm is fourth-order Runge–Kutta with a documented step-convergence test.

The weak-curvature limit has `f=18β(A+B)+O(β²)` and constraint

\[
 0=6\beta(3H^2-\Lambda)+O(\beta^2),
\]

recovering the **vacuum** Friedmann relation `H²=Λ/3`. The limit `β→0` is singular in the acceleration formula since `f_{AA}=O(β²)`; regular GR solutions form a constrained submanifold, while additional higher-curvature modes need separate stability analysis. Pereira's spectrum result is a reason to examine those modes carefully.

## 4. A complete synthetic vacuum branch

Use dimensionless units `H_*=1`, `b=β H_*²=0.02`, and `h=H/H_*`. These are a numerical stress test near the curvature scale set by β. The physical late-Universe value for Planck-scale β would be enormously smaller. Choose `h(0)=1` and `dh/d(H_*t)|_0=-0.01`, and calibrate the constant Λ from the **exact de Sitter background**, `\dot h=0`:

\[
 \lambda_{\rm dS}(h,b)=\frac{f(h^2,h^2)-h^2 f_A(h^2,h^2)}{6b}
 \qquad(f_A=f_B\text{ at }A=B).
\]

`b=0.02` gives `λ=2.9693009698787556` in units of `H_*²`. The non-de Sitter initial `\dot h=-0.01` then excites the higher-curvature vacuum mode while holding Λ fixed. Evolution yields:

| z | H/H* | min G eigenvalue | Λ_G/H*² |
|---:|---:|---:|---:|
| 0.0 | 1.000000000 | 1.041232820 | 0.446738582 |
| 0.2 | 1.002172419 | 1.041298931 | 0.449817659 |
| 0.4 | 1.003927228 | 1.041625089 | 0.455637268 |
| 0.6 | 1.004538090 | 1.042061642 | 0.461917780 |
| 0.8 | 1.003799920 | 1.041997252 | 0.466742700 |
| 1.0 | 1.001868189 | 1.041829013 | 0.468916432 |
| 1.2 | 0.999094262 | 1.041588085 | 0.467964400 |

The maximum reported absolute lapse constraint residual is below `10^-17`. Redshift-grid values converge within `5×10^-9` in both H and its first time derivative when the numerical step shrinks from 0.005 to 0.001.

Passing `E²=(H/H*)²` through TOE-03's seven-point synthetic covariance and profiling out the **unconstrained** basis `1,(1+z)²,(1+z)³,(1+z)⁴` gives:

\[
 \chi^2_{\rm profiled,synth}=0.0002517018845944183,\qquad
 \sqrt{\chi^2}=0.0158651153350.
\]

This is a **norm under an invented measurement covariance**, not an observational likelihood or a cosmological constraint. It shows how strongly a sample vacuum correction is obscured by the conventional background nuisance space under these particular declared uncertainties.

## 5. Limits and continuation

The paper's dressed fluid `\mathcal T_{\mu\nu}` couples metric and G-field; its conservation law is joint rather than standalone ordinary matter conservation. One must reduce the **complete matter Euler–Lagrange system** before producing a physical matter-plus-radiation expansion history. Substituting `ρ(a)` into the already-reduced vacuum action would confuse the constrained fluid variables and matter Lagrangian. Likewise, a scalar-only G-field ansatz would discard four other isotropic eigenmodes and lose source fidelity.

Prospective work: derive a consistent lapse-constrained perfect-fluid minisuperspace including Bianconi's dressed matter, test spatial curvature, then check any solutions against actual expansion-data covariance. Independent analytical checks should compare the vacuum reduction to the full covariant field equations (46)–(49), including the spatial equation and branch stability.

Run:

```sh
python -m unittest tests.test_toe04_gfield -v
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/TOEFLRW.lean
```

Source files: [`gfield_flrw.py`](gfield_flrw.py), [`gfield_vacuum_synthetic.json`](fixtures/gfield_vacuum_synthetic.json), [`test_toe04_gfield.py`](../../tests/test_toe04_gfield.py). The numerical receipt is reproducible with `research.toe.gfield_flrw.reference_experiment()`.

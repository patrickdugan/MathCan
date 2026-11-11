# TOE-04: Homogeneous vacuum ΛGfE, positive G-field spectra and H(z)

**2026-11-11 · Scope:** a source-based *spatially-flat vacuum* sector and numerical branch of the reduced action. The coupled matter field equations, full covariant verification, and observed cosmological data remain open.

## Sources and attribution

Bianconi, [Λ-Gravity from Entropy](https://arxiv.org/abs/2610.34496), equations (5), (16), (19), (31) and (45)–(49), establishes the metric-to-G constraint, emergent cosmological contribution and auxiliary-volume term. The five sectors and multiplicities are in Bianconi, [Thermodynamics of GfE](https://arxiv.org/abs/2510.22545), section III.1. Pereira's [Vacuum gravity from entropy](https://doi.org/10.1103/lxlj-ppwh) provides an independent quadratic-curvature coefficient check and a warning concerning additional propagating modes.

The FLRW lapse reduction, expanding-branch acceleration formula, numerical trajectory and tests below are MathCan derivations.

## Isotropic curvature and G eigenvalues

In FLRW with lapse N, scale factor a and spatial curvature k,

\[
A=N^{-2}\left(\ddot a/a-\dot a\dot N/(aN)\right),
\qquad
B=(\dot a^2/N^2+k)/a^2.
\]

With N=1, A=H²+dot H and B=H²+k/a². In vacuum the eigenvalues of U=beta times curvature, together with the G-field, are:

| Form sector | u | Multiplicity |
|---|---|---:|
| scalar | 6 beta (A+B) | 1 |
| temporal vector | 3 beta A | 1 |
| spatial vectors | beta (A+2B) | 3 |
| temporal bivectors | 2 beta A | 3 |
| spatial bivectors | 2 beta B | 3 |

Each G eigenvalue equals 1/(1-u). The physical positivity domain is 1-u>0 for all five sectors, and for beta>0

\[
\Lambda_{\mathcal G}={1\over6\beta}\sum_i z_i
(\mathcal G_i-1-\ln\mathcal G_i)\ge0.
\]

The Python module additionally evaluates the *algebraic* dressed perfect-fluid shifts from Bianconi's equation (49). Fluid dynamics are intentionally left unclosed.

## Metric-only action and the Λ constraint

Eliminating the algebraic G constraint in **vacuum** yields

\[
f(A,B)=-\sum_i z_i\ln[1-\beta(c_{Ai}A+c_{Bi}B)].
\]

The source volume term is L_Lambda=(6 beta Lambda/omega)(omega-s) with s=sqrt(-g). It vanishes on shell at omega=s, yet its *metric variation at fixed omega* gives

\[
\delta_s(sL_\Lambda)|_{\omega=s}=-6\beta\Lambda\,\delta s.
\]

Thus the reduced **metric first variation**, after treating the volume constraint properly, is equivalent to varying S proportional to the integral of N a³ [f(A,B)-6 beta Lambda] dt. Eliminating omega prematurely would discard the constant contribution.

At first order f=3 beta R. The quadratic curvature trace is

\[
\sum_i z_i(c_{Ai}A+c_{Bi}B)^2
=60A^2+84AB+60B^2
=5R_{\mu\nu}R^{\mu\nu}+\mathrm{GB},
\quad \mathrm{GB}=24AB.
\]

This matches the independent vacuum quadratic-curvature normalization from Pereira, modulo the 4D Gauss-Bonnet term. The nine Lean lemmas in MathCan/TOEFLRW.lean check degeneracies and curvature polynomial coefficients.

## Strictly convex curvature action

Let d_i=1-beta(c_Ai A+c_Bi B). Then

\[
f_{XY}=\sum_i {z_i\beta^2c_{Xi}c_{Yi}\over d_i^2},
\quad
v^\top \nabla^2 f\,v=\sum_i z_i
\left[{\beta(c_{Ai}v_A+c_{Bi}v_B)\over d_i}\right]^2.
\]

Since (3,0) and (0,2) occur among the sector directions, the Hessian is strictly positive definite for beta>0 and d_i>0. In particular f_AA>0.

## The lapse constraint and the numerical ODE

Vary the lapse N before setting N=1, including its time derivative in A. For k=0,

\[
0=f-6\beta\Lambda+(H^2-\dot H)f_A-2H^2f_B+H\dot f_A,
\quad
\dot f_A=f_{AA}(\ddot H+2H\dot H)+2H\dot H f_{AB}.
\]

This is affine in Hddot and uniquely determines the acceleration for H>0:

\[
\boxed{\ddot H=
{6\beta\Lambda-f-(H^2-\dot H)f_A+2H^2f_B
 -2H^2\dot H(f_{AA}+f_{AB})\over H f_{AA}}}.
\]

The numerical model uses dz/dt=-(1+z)H. Diffeomorphism invariance relates the spatial Euler equation to the lapse constraint on expanding branches; checking both directly against the full covariant field equations remains a separate proof obligation.

The small-beta constraint is 0=6 beta (3H²-Lambda)+O(beta²), reproducing **vacuum** GR. The formula for Hddot has a singular beta→0 limit, reflecting the additional higher-curvature mode.

## Synthetic branch and observability

Take dimensionless beta H_*²=0.02, H(0)/H_*=1, Hdot(0)/H_*²=-0.01. Hold the constant Lambda at its exact de Sitter background value,

\[
\Lambda_{\rm dS}(H,\beta)=
{f(H^2,H^2)-H^2f_A(H^2,H^2)\over6\beta}
=2.9693009698787556
\]
in units of H_*².

| Redshift z | H/H* | Smallest G eigenvalue | Lambda_G/H*² |
|---:|---:|---:|---:|
| 0.0 | 1.000000000 | 1.041232820 | 0.446738582 |
| 0.2 | 1.002172419 | 1.041298931 | 0.449817659 |
| 0.4 | 1.003927228 | 1.041625089 | 0.455637268 |
| 0.6 | 1.004538090 | 1.042061642 | 0.461917780 |
| 0.8 | 1.003799920 | 1.041997252 | 0.466742700 |
| 1.0 | 1.001868189 | 1.041829013 | 0.468916432 |
| 1.2 | 0.999094262 | 1.041588085 | 0.467964400 |

Numerical step refinement changes terminal H and Hdot by less than 5e-9; all five G eigenvalues remain positive and the lapse residual is smaller than 1e-12. Under TOE-03's deliberately **synthetic** seven-redshift covariance, freely profiling out the background functions 1, (1+z)², (1+z)³ and (1+z)⁴ gives a deviation norm squared of 0.0002517018845944183.

This beta is chosen as a high-curvature numerical stress test. For Planck-scale beta, beta times today's Hubble rate squared would be vastly smaller. This trajectory establishes neither a fit to observations nor a matter-inclusive ΛGfE prediction.

## Verification and next physics obligations

Use Python module research.toe.gfield_flrw to print a reproducible receipt, run tests/test_toe04_gfield.py, and build the MathCan Lean library. The nine kernel lemmas cover algebraic traces and polynomial coefficients. The log action, lapse variation, and ODE are supported by the written derivation and finite numerical checks.

The next step is a complete dressed-fluid minisuperspace and independent covariant-equation residual test, followed by realistic initial conditions, stability screening and measured H(z) covariance.

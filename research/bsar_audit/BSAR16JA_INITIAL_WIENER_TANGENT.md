# BSAR-16J-A: exact initial Fourier-Wiener and H4 truncation-error tangents

Parent task: [BSAR-16J #233](https://github.com/patrickdugan/MathCan/issues/233), following the [BSAR-16I core-transfer frontier #232](https://github.com/patrickdugan/MathCan/pull/232). The source data and original convolution come from BSAR-14, pinned Git blob aa25ad74be2347acf061d631f55338802eead212. The independent exact rational Galerkin split is the merged BSAR-16A implementation at commit ee55923801e5d85b90e6be654929d1a1fcfd3d5a.

**Purpose:** Measure exact time-zero frequency-weighted spatial truncation forcing in norms suited to a future full-PDE vorticity-core comparison. This stage is exact algebra on the initial datum. It establishes neither an interval error bound nor a quantitative strong-solution lifespan.

## Original exact datum and full-versus-Galerkin tangent

For the smooth periodic BSAR-14 initial field, let u denote the classical local full Navier–Stokes solution and v_K the exact finite Fourier–Galerkin ODE trajectory started from the same field. The Navier–Stokes equation and the Galerkin ODE give at t=0

\[
\left.\partial_t(u-v_K)\right|_{0}
=-r_K(0),\qquad
r_K(0)=P_{>K}\mathbb P[(u_0\cdot\nabla)u_0].
\]

The source is a finite trigonometric polynomial and is smooth. Standard local classical well-posedness is sufficient to interpret this initial derivative in every fixed Sobolev norm. This tangent identity applies at t=0, without independently providing a specific positive-time error enclosure or any uniform-in-N conclusion.

The registered roots are N=1/2, sigma=±1, A=1, nu=1/10, and the BSAR-15 strict retained cube cutoffs K=5,7,10 on grids M=16,24,32.

## Exact source-specific omitted modes

The source-pinned BSAR-14 rational convolution and Leray projection yield:

- N=1, K=5,7,10: exactly zero initial omitted forcing.
- N=2, K=10: exactly zero initial omitted forcing.
- N=2, K=5 or 7: the **only** omitted coefficients are at k=±(2,8,0), each with value sigma*(2/17,-1/34,0).

The relevant wavevector has squared length 68. The squared magnitude of either Gaussian-rational omitted coefficient is 1/68. The source-parity tests compare all resulting omitted coefficients independently against the original BSAR-14 exact convolution and projector.

## Three norm weights and one tangent

On the flat 2pi-periodic three-torus use spatial-average normalized Parseval and define

\[
\|e\|_{L^2}^2=\sum_k|\hat e(k)|^2,\qquad
\|e\|_{\mathcal A^1}=\sum_k|k|\,|\hat e(k)|,\qquad
\|e\|_{H^4}^2=\sum_k(1+|k|^2)^4|\hat e(k)|^2.
\]

The A1 norm is the Fourier-Wiener derivative-weighted l1 norm. It directly controls the pointwise vorticity perturbation by

\[
\|\nabla\times e\|_\infty\le\sum_k|k|\,|\hat e(k)|=\|e\|_{\mathcal A^1}.
\]

At N=2 with K=5/7, the omitted pair gives the following **exact** values:

| Initial derivative observable | Exact squared/norm value |
|---|---|
| Velocity L2 square | 1/34 |
| Fourier-Wiener A1 norm | 2 |
| Vorticity L2 square | 2 |
| Inhomogeneous velocity H4 square | 69^4/34 = 22667121/34 |

The H4 derivative norm is 4761/sqrt(34), approximately 816.5. The A1 derivative norm is exactly 2. The extreme difference comes from the H4 weight at squared wavevector length 68. The H4 sufficient core-transfer criterion from BSAR-16I is rigorous but very stringent for these two coarse Galerkin cutoffs; a source-specific A1 residual/control inequality is a promising alternative.

At the same time the initial omission at K=10 is exactly zero, and that alone cannot control the high modes created by the nonlinear PDE after positive time.

## Interpretation of the exact tangent

For each fixed source/cutoff with a locally smooth full NSE solution, the initial derivative identity implies

\[
\lim_{t\downarrow0}
\frac{\|u(t)-v_K(t)\|_{\mathcal A^1}}t
=\|r_K(0)\|_{\mathcal A^1},
\]

provided the local classical solution is differentiable at zero in the Fourier-Wiener A1 norm. Smooth trigonometric data and classical local Sobolev regularity of sufficiently high order justify the required A1 continuity via a Fourier-Sobolev embedding. The analogous H4 limit holds by differentiability in H4 for sufficiently smooth data.

These are local tangent relations. The numerical estimate t*2 at T=0.012 would be approximately 0.024, which **must not** be treated as an error bound: positive-time mode generation and nonlinear amplification require their own rigorous control.

## Verification and next mathematical gate

The standard-library Python module directly evaluates BSAR-16A's Gaussian-rational high-mode forcing and computes exact weighted Fourier sums using integer square-root checks. It freezes twelve source/phase/grid records, with four nonzero high-mode cases, explicit original provenance and SHA-256. No FFT, floating arithmetic or unverified time step enters this certificate.

Reproduce:

    python -m unittest experiments.bsar16.test_initial_wiener_tangent -v
    python -m experiments.bsar16.initial_wiener_tangent generate --out /tmp/bsar16ja
    python -m experiments.bsar16.initial_wiener_tangent audit --out /tmp/bsar16ja

The next requirement in [BSAR-16J #233](https://github.com/patrickdugan/MathCan/issues/233) is a time-uniform a posteriori full-PDE error bound in A1 (or another norm directly controlling curl), with a quantitative strong-solution existence interval when necessary. An A1 error upper bound of 3/20 through T=3/250 would transfer the BSAR-16C original anchors to the true full-PDE half-maximum vorticity core with the conservative margin and direction witnesses from BSAR-16I.

This work follows a recognized a posteriori approximate-solution approach for Navier–Stokes, for example Morosi and Pizzocchero (Nonlinear Analysis 75, 2012, DOI 10.1016/j.na.2011.10.020), and Chernyshenko, Constantin, Robinson and Titi (J. Math. Phys. 48, 2007, DOI 10.1063/1.2372512). It establishes no long-time or global 3D regularity claim.

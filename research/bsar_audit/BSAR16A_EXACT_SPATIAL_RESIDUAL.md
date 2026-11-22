# BSAR-16A: exact initial spatial-truncation residual and finite Galerkin energy audit

Parent: [BSAR-16 #213](https://github.com/patrickdugan/MathCan/issues/213). Source:
[BSAR-14 exact triad](https://github.com/patrickdugan/MathCan/pull/208);
[BSAR-15 numerical Galerkin study](https://github.com/patrickdugan/MathCan/pull/210).

**Evidence scope:** an independent Gaussian-rational calculation for the *exact initial field* and exact finite-dimensional Galerkin vector field, at \(t=0\). This is the first spatial-residual gate only. A rigorous error enclosure over \(0\le t\le0.012\), a validated RK4 integrator, outward-rounded core geometry, and any claim about the global 3D Navier–Stokes solution remain separate open tasks.

## Definitions and Fourier normalization

Work on the \(2\pi\)-periodic flat three-torus with

\[
v(x)=\sum_{k\in\mathbb Z^3}\widehat v_k e^{ik\cdot x},
\quad
\|v\|_2^2=(2\pi)^{-3}\int_{\mathbb T^3}|v|^2dx
=\sum_k|\widehat v_k|^2.
\]

For BSAR-15 grid size \(M\), the strict 2/3 retained cube is

\[
\Lambda_K=\{k\in\mathbb Z^3: \max_j|k_j|\le K\},
\qquad K=\lfloor(M-1)/3\rfloor.
\]

Let \(P_{\le K}\) be Fourier projection onto this cube, with zero mean, and \(\mathbb P_k=I-kk^\top/|k|^2\) the incompressible Leray projector for \(k\ne0\). The exact continuous-time finite Galerkin system is

\[
\partial_t v_K+\nu(-\Delta)v_K+
P_{\le K}\mathbb P[(v_K\cdot\nabla)v_K]=0.
\]

It is an ODE with a quadratic polynomial vector field. The full-PDE defect of its exact solution is

\[
r_K=\partial_t v_K+\nu(-\Delta)v_K+
\mathbb P[(v_K\cdot\nabla)v_K]
=P_{>K}\mathbb P[(v_K\cdot\nabla)v_K].
\]

The exact convolution coefficient at wavevector \(k\) is

\[
\widehat B_k=\sum_{p+q=k}i\,(\widehat v_p\cdot q)\widehat v_q.
\]

The independent verifier evaluates this sum and the rational Leray projection without FFT, floating-point rounding, or aliasing.

## Exact time-zero results

The eight BSAR-14 source coefficients are reconstructed independently and compared with the original exact verifier. The registered phase-matched roots have \(N\in\{1,2\}\), \(\sigma\in\{-1,+1\}\), \(A=1\), and \(\nu=1/10\).

| Initial frequency | Phase | M=16, K=5 | M=24, K=7 | M=32, K=10 |
|---|---|---:|---:|---:|
| N=1 | -1 | 0 | 0 | 0 |
| N=1 | +1 | 0 | 0 | 0 |
| N=2 | -1 | 1/34 | 1/34 | 0 |
| N=2 | +1 | 1/34 | 1/34 | 0 |

Each entry is the exact squared spatial-average \(L^2\) norm \(\|r_K(0)\|_2^2\), rather than \(\|r_K(0)\|_2\). Consequently the high-mode residual norm for \(N=2\), \(M=16\) or 24 is \(1/\sqrt{34}\).

The only nonzero omitted Leray-projected coefficients in those two cases are

\[
\widehat r_K(\pm(2,8,0))
=\sigma(2/17,-1/34,0).
\]

For each coefficient, \(k\cdot\widehat r_K=0\) holds exactly. Its squared Euclidean norm is \(1/68\), and the conjugate pair yields \(1/34\). The signed coefficients reverse under \(\sigma\mapsto-\sigma\), while their squared norms agree.

For \(N=1\), the initial quadratic forcing lies within the smallest retained cube. The same holds for \(N=2\), \(K=10\). **Zero high-mode residual at \(t=0\) implies no bound on its positive-time value**, since the Galerkin solution creates new modes. In particular, BSAR-15's close energy agreement between grids is compatible with the exact \(N=2\), \(K=7\) high-mode forcing being nonzero initially.

## Immediate implication for full-PDE versus Galerkin tangents

The exact full Navier–Stokes time derivative from the smooth BSAR-14 datum and the Galerkin ODE time derivative have the same viscous term, because the initial field is wholly retained. Their difference is exactly

\[
\left.\partial_t(u-v_K)\right|_{t=0}=-r_K(0).
\]

Local smooth well-posedness for this trigonometric initial datum and the smooth finite Galerkin ODE therefore imply the short-time asymptotic

\[
\lim_{t\downarrow0}\frac{\|u(t)-v_K(t)\|_2}{t}
=\|r_K(0)\|_2.
\]

For \(N=2\), \(K=5\) or \(7\), this limit is exactly \(1/\sqrt{34}\approx0.1714985851\); for the other registered source/grid pairs the linear coefficient is zero. The result is **a local tangent statement**, with no certified remainder or quantitative interval of validity. A close *scalar kinetic-energy* match between different Galerkin grids can coexist with a nonzero first-order difference between their full Fourier velocity fields. This motivates full-field error auditing rather than interpreting BSAR-15's small energy discrepancy as spatial convergence of the solution.

## Energy algebra

Set

\[
E_K=\tfrac12\sum_{k\in\Lambda_K}|\widehat v_k|^2,\qquad
D_K=\sum_{k\in\Lambda_K}|k|^2|\widehat v_k|^2.
\]

On real, mean-zero, divergence-free trigonometric fields, the projection is self-adjoint and \(\int v\cdot(v\cdot\nabla)v=0\). Thus every exact finite Galerkin ODE trajectory satisfies

\[
\frac{dE_K}{dt}=-\nu D_K.
\]

This is an analytic finite-dimensional identity. The independent verifier checks its Gaussian-rational Fourier form on all four BSAR-14 roots and on an additional divergence-free reality-paired perturbation. It finds \(E_K(0)=2\), \(D_K(0)=31N^2/2\), zero nonlinear energy power, and \(\dot E_K(0)=-(31/20)N^2\). The script is a standalone exact-arithmetic checker, **not a Lean kernel proof of the general identity**. A floating-point RK4 energy-balance defect is a separate numerical quantity.

## Conditional route to a full-PDE error enclosure

Suppose a smooth incompressible Navier–Stokes solution \(u\) exists on \([0,T]\) with the registered initial data, and \(v_K\) is the exact continuous-time finite Galerkin solution from the same data. Put \(e=u-v_K\). Subtraction gives

\[
\partial_t e+\nu(-\Delta)e+
\mathbb P[(u\cdot\nabla)e+(e\cdot\nabla)v_K]=-r_K.
\]

Testing against \(e\), using \(\nabla\cdot u=\nabla\cdot e=0\), yields

\[
\frac12\frac{d}{dt}\|e\|_2^2+\nu\|\nabla e\|_2^2
\le\|\nabla v_K\|_\infty\|e\|_2^2+
\|r_K\|_2\|e\|_2.
\]

In particular, while the smooth solution exists and since \(e(0)=0\),

\[
\|e(t)\|_2\le
\int_0^t\|r_K(s)\|_2\,
\exp\left(\int_s^t\|\nabla v_K(\tau)\|_\infty\,d\tau\right)\,ds.
\]

This estimate requires **time-uniform certified enclosures** of the exact Galerkin path's residual and its gradient. For BSAR-15's computed RK4 path, a separate validated dense interpolant and a roundoff-inclusive ODE defect must be added to the residual. None of those positive-time bounds follow from the time-zero rational certificates here. Control of vorticity and the half-maximum core additionally needs stronger regularity or derivative-error estimates. The mathematical PDE-derived ratio budget in [BSAR-09 #186](https://github.com/patrickdugan/MathCan/issues/186) remains open.

## Reproduce

From the MathCan repository root, with Python 3.11 and standard library only:

~~~sh
python -m unittest experiments.bsar16.test_exact_residual -v
python -m experiments.bsar16.exact_residual generate --out /tmp/bsar16a
python -m experiments.bsar16.exact_residual audit --out /tmp/bsar16a
~~~

The twelve certificates and SHA-256 manifest are archived by the dedicated workflow. The original BSAR-14 source is pinned to its Git blob \`aa25ad74be2347acf061d631f55338802eead212\`; independent mode and every projected nonlinear coefficient must match that oracle. The row-list SHA-256 is

\`f5cd7df385430f011419db8faf5b515747a0ad20942eb09ef20fc85d4cea3fe4\`.

## Next BSAR-16 milestone

Construct a validated time-dependent Galerkin enclosure, including RK4 local/global defects and roundoff, then bound \(\|r_K(t)\|_2\) and \(\|\nabla v_K(t)\|_\infty\) across a registered short interval with an exact convolution or outward-rounded interval computation. Audit the \(N=2\) source first, where the finite truncation residual is already nonzero at time zero. Only after that can the conditional \(L^2\) PDE estimate become a numerical upper bound on a specified smooth interval.

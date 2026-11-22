# BSAR-15: short-time, dealiased three-dimensional Navier–Stokes Galerkin experiment

**Research objective:** Extend [BSAR-14's exact time-zero Fourier transfer](https://github.com/patrickdugan/MathCan/pull/208) into a reproducible short-time numerical study of the full three-dimensional periodic incompressible Navier–Stokes dynamics. The corresponding task is [BSAR-15 issue #209](https://github.com/patrickdugan/MathCan/issues/209). The still-open mathematical endpoint is [the PDE-derived dimensionless window budget](https://github.com/patrickdugan/MathCan/issues/186).

The source of the initial data is the kernel-independent exact Gaussian-rational verifier at MathCan merge e2c0e1c56f6e5d2291536156709f75668d1e0f8f. The external BSA-R source is pinned at VivienSweetbrier/bsa-r@80c62433b0eb671175bd8d6169822d3ebd922b60.

## Smooth divergence-free initial field

On the flat 2π-periodic three-torus take N=1 or 2, A=1 and phase σ∈{−1,+1}:

\[
\begin{aligned}
u_x(x,y,z,0)&=A[\cos(2Ny)+2\sigma\sin(Nx+2Ny)+\cos Nz],\\
u_y(x,y,z,0)&=A[\cos Nx-\sigma\sin(Nx+2Ny)],\\
u_z(x,y,z,0)&=0.
\end{aligned}
\]

There are four real Fourier-mode pairs. They have exactly zero divergence, initial spatial-average energy E(0)=2A² and enstrophy D(0)=(31/2)A²N². The exact BSAR-14 Leray-projected nonlinear shell transfers are

\[
(T_1,T_4,T_5)=\sigma A^3N(1/4,-1,3/4),
\]

with \(\sum_jT_j=0\), where shell j means |k|²=jN². A previously absent genuine three-dimensional mode k=(N,0,N) has exact Fourier derivative

\[
\left.\frac{d\hat u_k}{dt}\right|_0
=(0,-iA^2N/4,0).
\]

The numerical solver creates its initial Fourier array directly from the exact source coefficients, rather than from sampled trigonometric functions. Its first nonlinear evaluation is compared to those exact fractions.

The smooth periodic initial field has a smooth local Navier–Stokes evolution by standard local well-posedness. The numerical experiment is a finite-dimensional spectral approximation to that evolution, and does not purport to close the infinite-dimensional Fourier hierarchy.

## Spatial discretization and pressure

For M grid points along each coordinate, the velocity is represented by normalized Fourier coefficients \(\hat u(k)\) on the cube of M discrete wavevectors. Each retained mode satisfies \(k\cdot\hat u(k)=0\). The nonlinear term is evaluated as \((u\cdot\nabla)u\) using spectral derivatives and pointwise products followed by FFT. The pressure is eliminated with the Leray multiplier

\[
P_k v=v-\frac{k(k\cdot v)}{|k|^2},\qquad k\ne0.
\]

At k=0 the mean is fixed to zero. The Fourier ODE solved numerically is

\[
\frac{d\hat u(k)}{dt}=
-P_k\widehat{(u\cdot\nabla)u}(k)
-\nu|k|^2\hat u(k).
\]

A strict 2/3 cutoff keeps \(\max_i|k_i|\le\lfloor(M-1)/3\rfloor\) in all three directions. This protects the **retained quadratic convolution** from FFT wraparound aliasing under the standard 2/3 rule, while introducing a finite Fourier truncation. The velocity is advanced by explicit fourth-order Runge–Kutta with projection at every nonlinear evaluation and after each complete step.

No claim is made that a 2/3 dealiased Fourier polynomial is the exact infinite-dimensional Navier–Stokes solution. The experiment uses double-precision FFTs without interval rounding or certified truncation/time-stepping bounds.

## Registered parameters and comparisons

| Parameter | Registered values |
|---|---|
| Initial frequencies N | 1, 2 |
| Matched phases σ | −1, +1 |
| Initial amplitude A | 1 |
| Viscosity ν | 0.1 |
| End time T | 0.012 |
| Spatial grid | M=16, 24, 32 |
| Standard time step | 0.001 |
| Fine time-step control | 0.0005 on M=32 |
| Runs | 16 numerical trajectories |

Both initial Fourier components ±(N,2N,0) lie within each grid's 2/3 retained cutoff. The source-matched phase controls share the identical initial shell-energy spectrum and reverse the signs of the three nonlinear shell transfers. The campaign records the first observed transfer-sign reversal for each initial shell, if one occurs. Any sign persistence has been measured only over the finite registered time window.

At T, the script compares M=24 with M=32 at fixed step size, and Δt=0.001 with Δt=0.0005 at M=32. Absolute differences in energy and a newly generated mode are reported. These are **empirical inter-resolution discrepancies**, not guaranteed upper bounds for PDE error. The script also records the trapezoidal energy defect

\[
E(T)-E(0)+\nu\operatorname{Trapz}_{\Delta t}\int_0^TD(t)\,dt
\]

as a numerical conservation diagnostic. The exact Galerkin ODE conserves nonlinear kinetic energy, but the RK4 discretization has a truncation error and the trapezoidal integral introduces additional quadrature error.

## Evolving vorticity core and geometric receipts

For each stored snapshot, the numerical vorticity is reconstructed from

\[
\hat\omega(k,t)=ik\times\hat u(k,t).
\]

The script reports the grid-sampled maximum \(M_{\omega,\mathrm{grid}}\), fraction of sampled points with \(|\omega|\ge M_{\omega,\mathrm{grid}}/2\), near-zero fraction, and a sampled direction quotient over a specified set of offsets.

**The grid-relative sampled-core quotient is only an observational statistic.** Some sampled points may fail the actual continuum half-maximum criterion if the true maximum exceeds the grid maximum. In particular, one cannot label the sampled maximum a certified lower bound on the BSA-R continuum cone seminorm without checking both endpoints against the true core.

For an independent fixed pair, use the two BSAR-14 source anchor points

\[
x_0=(0,0,\pi/(2N)),\qquad
x_1=(\pi/N,0,\pi/(2N)).
\]

Their spacing is exactly π/N and both are grid nodes on all registered M. At t=0 they lie inside the true high-vorticity core, with normalized direction difference squared 50/13.

The exact initial trigonometric field satisfies

\[
\sup_x|\omega(x,0)|\le\sqrt{65}\,AN.
\]

For the finite Galerkin field at time t, the Fourier triangle inequality gives the continuum upper envelope

\[
\sup_x|\omega_M(x,t)|
\le\sqrt{65}\,AN+
\sum_{k}|\hat\omega_M(k,t)-\hat\omega_M(k,0)|.
\]

This can be evaluated from the computed finite coefficients. The two fixed anchor points are accepted as **continuum-core anchor candidates for the Galerkin polynomial** only when both reconstructed magnitudes exceed half this upper envelope. For such a pair, their numerical normalized-direction difference divided by π/N provides a lower witness for the Galerkin cone seminorm.

A separate spatial Lipschitz envelope uses

\[
L_\omega(t)=\sum_{k}|k|\,|\hat\omega_M(k,t)|.
\]

Because any true high-core endpoint has magnitude at least \(M_{\omega,\mathrm{grid}}/2\), the vector-normalization inequality and the trivial diameter bound imply the finite-polynomial upper envelope

\[
K_{\xi,M}(t)\le\frac{8L_\omega(t)}{M_{\omega,\mathrm{grid}}(t)}.
\]

These inequalities are valid for a finite Fourier polynomial and periodic geodesic distances. Their **floating-point evaluations are not certified outward intervals**. Accordingly, the report always retains separate fields for the grid-relative sample, eligible anchor witness, and analytic finite-polynomial upper envelope.

## Registered numerical results

The [precision-preserving CI run](https://github.com/patrickdugan/MathCan/actions/runs/44999442590) passed the ten dedicated numerical/source tests and archived 16 runs. The source SHA-256 was 787b227115cfbc58ebf114aa8820e1155d2938adbfd2a050c3bc452b60aa5419. The archived normalized JSON run-list SHA-256 is 8a2997e207ab9b308de03d59aa25fee5f66327fb26a6a6003c61a94ac4b416bf.

The M=32, Δt=0.0005 trajectories at T=0.012 give:

| N | σ | E(T) | Imaginary part of new-mode y coefficient | Trapezoidal energy defect | Galerkin core-anchor lower witness |
|---|---:|---:|---:|---:|---:|
| 1 | −1 | 1.981502444602 | −0.002975007006 | 4.44e−10 | 1.223109528 |
| 1 | +1 | 1.981502512310 | −0.003010745983 | 3.87e−10 | 1.224478258 |
| 2 | −1 | 1.927219852383 | −0.005873249513 | 2.35e−8 | 2.441873516 |
| 2 | +1 | 1.927221962035 | −0.006013125111 | 2.17e−8 | 2.447502370 |

The initial source-mode derivative predicts an imaginary y-component of −N t/4, hence −0.003 for N=1 and −0.006 for N=2 at this horizon. The observed differences agree with the expected nonlinear and viscous curvature away from the tangent approximation. All three initial shell-transfer signs persisted in every registered numerical run through T=0.012; no claim is made beyond that interval.

Comparing M=24 and M=32 at fixed Δt=0.001 yielded energy discrepancies at most 2.38e−9 and new-mode coefficient discrepancies at most 1.04e−9. At M=32, comparing Δt=0.001 and 0.0005 yielded energy discrepancies at most 2.19e−13 and new-mode differences at most 2.11e−14. These are empirical numerical self-comparisons, and the small values do not certify any upper bound for truncation error relative to the true infinite-dimensional PDE.

The 24³ and 32³ grid-relative sampled-core fractions differed by up to 0.01881 (about 1.9 percentage points). At M=32, the two source-derived anchor points remained eligible under the finite Galerkin global-max envelope for all three recorded times. Their final lower witnesses ranged from 1.223 to 1.224 for N=1, and from 2.442 to 2.448 for N=2. The finite-polynomial Lipschitz upper envelopes were substantially wider (about 17.4–17.5 and 35.5–35.8 respectively). These refer exclusively to the **computed Galerkin trigonometric fields**, evaluated in floating point without outward rounding.

The fact that low-mode energy and generated-mode coefficients agree closely across grids while grid-sampled core fraction differs is a reason to prioritize vorticity-core geometry in the next spatial-resolution study.

## Verification and interpretive limits

The [standalone numerical module](../../experiments/bsar15/galerkin.py) depends on NumPy, installed **only in the dedicated BSAR-15 workflow**. MathCan's core Init-only Lean library and standard Python dependencies remain unchanged.

The dedicated checks test source coefficient parity, exact time-zero projected nonlinear derivatives, zero convective energy power, divergence control, Galerkin energy dissipation, new-mode generation, matched transfer signs, high-core anchor eligibility, and resolution/time-step comparisons. Source hashes and a deterministic scenario manifest accompany every archived result.

Reproduce:

    python -m pip install "numpy==2.3.5"
    python -m unittest experiments.bsar15.test_galerkin -v
    python -m experiments.bsar15.galerkin --out /tmp/bsar15

This is a **numerical short-time Galerkin experiment**, not a formal proof of smooth Navier–Stokes evolution for arbitrary data, a frequency-uniform lifetime, or a rigorous time-integrated cone budget. The PDE-derived bound on the BSA-R window ratio sum \(\sum I_m/M\) remains open. In particular, the registered numerical times do not establish uniform estimates as frequency increases, as viscosity vanishes, or as a hypothetical singularity is approached.

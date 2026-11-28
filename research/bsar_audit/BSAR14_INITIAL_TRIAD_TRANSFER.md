# BSAR-14: a 3D Navier–Stokes initial datum with exact triad energy transfer

This extends [BSAR-13](https://github.com/patrickdugan/MathCan/pull/204), whose nonzero ABC advection is canceled entirely by pressure. BSAR-14 supplies smooth periodic divergence-free **initial data** with a nonzero Leray-projected convective term, instantaneously transferring kinetic energy between already populated Fourier shells and creating a genuinely three-dimensional new Fourier mode.

The experiment is registered as [MathCan issue #207](https://github.com/patrickdugan/MathCan/issues/207). All calculations refer to the periodic three-torus (R/2πZ)^3, with spatial averages normalized by its volume and viscosity ν>0.

## Explicit divergence-free initial field

For integer N≥1, positive rational amplitude A, and phase σ∈{−1,+1}, define

\[
\begin{aligned}
u_x(x,y,z,0)&=A\bigl[\cos(2Ny)+2\sigma\sin(Nx+2Ny)+\cos(Nz)\bigr],\\
u_y(x,y,z,0)&=A\bigl[\cos(Nx)-\sigma\sin(Nx+2Ny)\bigr],\\
u_z(x,y,z,0)&=0.
\end{aligned}
\]

The divergence vanishes identically: ∂x u_x=2σAN cos(Nx+2Ny) and ∂y u_y=−2σAN cos(Nx+2Ny). The field has zero mean and depends on all three spatial coordinates. Its eight real Fourier coefficients occupy ±(N,0,0), ±(0,2N,0), ±(N,2N,0), and ±(0,0,N).

Smooth 3D periodic divergence-free initial data have a unique smooth Navier–Stokes solution for a local time interval. This finite Fourier support is **initial only**: the nonlinear dynamics create new modes, so an exact finite-mode ansatz for a positive time interval is not asserted.

## Leray projection reveals actual nonlinear transfer

Let \(\mathcal N=(u\cdot\nabla)u\) at t=0. For k≠0 its Fourier coefficient is

\[
\widehat{\mathcal N}(k)=i\sum_{p+q=k}
(q\cdot\hat u(p))\hat u(q).
\]

The exact pressure coefficient solving the incompressibility constraint is

\[
\hat p(k)=\frac{i\,k\cdot\widehat{\mathcal N}(k)}{|k|^2}.
\]

Its gradient cancels the longitudinal part of advection. Thus the **solenoidal forcing** in the initial PDE derivative is

\[
P_k\widehat{\mathcal N}(k)
=\widehat{\mathcal N}(k)
-\frac{k(k\cdot\widehat{\mathcal N}(k))}{|k|^2},
\qquad
\partial_t\hat u(k,0)=-\nu|k|^2\hat u(k,0)
-P_k\widehat{\mathcal N}(k).
\]

The source [Gaussian-rational checker](../../scripts/bsar14_initial_triad_transfer.py) computes every convolution and pressure coefficient, confirms that k·P_k N_k=0 and that negative wavevectors carry the complex conjugate coefficient. It also checks all initial shell-energy receipts against an independent exact transfer formula.

Take normalized shell energies \(E_j=\frac12\sum_{|k|^2=jN^2}|\hat u(k)|^2\). At the initial instant they are

| Shell j | Initial energy \(E_j\) | Nonlinear energy derivative \(T_j\) |
|---|---|---|
| 1 | \(A^2/2\) | \(\sigma A^3N/4\) |
| 4 | \(A^2/4\) | \(-\sigma A^3N\) |
| 5 | \(5A^2/4\) | \(3\sigma A^3N/4\) |

The three nonlinear derivatives sum exactly to zero, as required for unforced incompressible kinetic-energy transfer. For σ=+1, shell 4 loses energy while shells 1 and 5 gain it; the transfer reverses for σ=−1. The **initial energy spectrum is identical** for both phases, and this exact matched control verifies that the transfer sign depends on interaction phase.

The initial enstrophy density and total kinetic-energy derivative are

\[
D(0)=\frac{31}{2}A^2N^2,\qquad
E(0)=2A^2,\qquad
\left.\frac{dE}{dt}\right|_0=-\frac{31}{2}\nu A^2N^2.
\]

Each shell also has a viscous contribution \(-2\nu jN^2E_j\); combining it with the nonlinear transfers reproduces the energy identity.

An unpopulated spatially three-dimensional mode k=(N,0,N) has

\[
P_k\widehat{\mathcal N}(k)=
\left(0,\frac{iA^2N}{4},0\right).
\]

Consequently \(\partial_t\hat u(k,0)=(0,-iA^2N/4,0)\neq0\). This establishes explicit instantaneous generation of a new Fourier mode by the solenoidal nonlinearity.

## Nonzero vorticity stretching and time-zero cone geometry

The vorticity of the initial field is

\[
\omega(0)=
\left(0,\;-AN\sin Nz,\;
-AN\sin Nx+2AN\sin 2Ny-5\sigma AN\cos(Nx+2Ny)\right).
\]

At x=y=0,z=π/(2N), exact differentiation gives

\[
(\omega\cdot\nabla)u
=\sigma A^2N^2(1,2,0)\neq0.
\]

This is genuine vortex stretching, with an exact pointwise Fourier evaluation using fourth roots of unity.

The BSA-R high-vorticity cone seminorm uses pairs of points with |ω| at least half the spatial maximum. Consider

\[
x_0=(0,0,\pi/(2N)),\qquad
x_1=(\pi/N,0,\pi/(2N)).
\]

The two vorticity vectors are \((0,-AN,-5\sigma AN)\) and \((0,-AN,+5\sigma AN)\). Both have squared magnitude \(26A^2N^2\). Globally \(|\omega|^2\le65A^2N^2\), so each is in the half-maximum core because \(4\cdot26>65\). Their direction difference squared is \(50/13\) and their torus separation is π/N. Consequently,

\[
K_\xi(0)\ge\frac{50N}{13\pi}>\frac{25N}{26},
\]

using π<4.

An upper bound is also available without defining ξ across any possible vortex zeros outside the core. The unnormalized gradient satisfies

\[
|\nabla\omega|_F^2\le
(1^2+6^2+14^2)A^2N^4
=233A^2N^4<256A^2N^4.
\]

The global vorticity maximum is at least \(\sqrt{26}AN\), so each core endpoint has |ω|≥\(\sqrt{26}AN/2>5AN/2\). For endpoints in the core, the standard normalization inequality gives

\[
|\xi(x)-\xi(y)|
\le\min\left(2,\frac{64}{5}N\,d_{\mathbb T^3}(x,y)\right).
\]

Taking the maximum of the squared quotient over distances yields

\[
\boxed{\frac{25}{26}N<K_\xi(0)\le\frac{128}{5}N<26N.}
\]

The geometric estimates are derived in this note. The checker exactly verifies the Fourier derivatives, anchor values and rational consequences. **This is a time-zero cone bracket**, not a space-time integral bound.

## Initial homogeneous Sobolev scaling

Set N=m⁴, A=m^(−q), \(s=q/4\), for m≥2 and q=0,1,2,3,4. The initial squared homogeneous H^s seminorm, under spatial-average normalization, is

\[
\|u(0)\|_{\dot H^s}^2
=A^2N^{2s}\left(1+\frac12\,2^{2s}
+\frac52\,5^s\right)
=1+\frac12\,2^{q/2}+\frac52\,5^{q/4}.
\]

It is independent of m, and for the five registered exponents lies in the explicit rational enclosure

\[
4\le\|u(0)\|_{\dot H^s}^2\le\frac{31}{2}.
\]

The Python verifier uses exact integer-power comparisons to enclose square and fourth roots by rational bounds, including the irrational q=1,2,3 weights. It never substitutes floating approximations.

The initial nonlinear shell transfer has scale \(A^3N=m^{4-3q}\). The cone integrand at time zero satisfies

\[
\frac{775}{52} A^2N^3
\le K_\xi(0)D(0)\le
403 A^2N^3.
\]

Thus the *instantaneous* cone integrand has scale \(m^{12-2q}\) for this source family. The time interval on which this rate persists depends on the actual nonlinear evolution and viscosity. It cannot be used to claim a corresponding integrated cone-cost divergence without further PDE estimates.

## Scope and next analytic gate

The source checks exact initial Fourier algebra, true non-gradient NSE nonlinear forcing, shell transfer, a newly generated 3D wavevector, and pointwise vortex stretching. It freezes 360 cases (12 base frequencies, five Sobolev exponents, three viscosities, and two opposite phases), with 180 phase-matched pairs and SHA-256 custody.

The work does not simulate or formally prove a full positive-time PDE solution, nor establish the unconditional bound on the BSA-R dimensionless sum \(\sum I_m/M\). In particular, the initial cone bracket and instantaneous energy transfer are mathematical diagnostics, while [BSAR-09 issue #186](https://github.com/patrickdugan/MathCan/issues/186) still requires a PDE-defined window cost and a uniform time-integrated estimate.

The next appropriate step is an independently controlled short-time PDE evolution study using divergence-free spectral projection, dealiased convolution, viscosity, time-step error bounds, and periodic energy budgets, with model-generated correction data kept separate from physical evidence.

# BSAR-13: exact 3D ABC Beltrami flow with active advection and pressure cancellation

This follows [BSAR-12's two-mode exact shear](https://github.com/patrickdugan/MathCan/pull/200). The two-mode construction has nonzero vorticity-direction harmonic tension but its velocity advection is identically zero. Here we test a genuinely three-dimensional, nonzero convective term that the pressure balances exactly. The target was registered in [BSAR-13 issue #203](https://github.com/patrickdugan/MathCan/issues/203).

## Exact periodic unforced Navier–Stokes solution

For a positive integer N, on the 2π-periodic 3-torus let

\[
U_N(x,y,z)=
(\sin Nz+\cos Ny,\quad
 \sin Nx+\cos Nz,\quad
 \sin Ny+\cos Nx).
\]

Direct differentiation establishes

\[
\nabla\cdot U_N=0,\quad
\nabla\times U_N=N U_N,\quad
\Delta U_N=-N^2U_N.
\]

For A>0, ν>0 take

\[
u=A e^{-\nu N^2t}U_N,\qquad
p=-\tfrac12 A^2 e^{-2\nu N^2t}|U_N|^2.
\]

The vector calculus identity

\[
(u\cdot\nabla)u=\nabla(|u|^2/2)-u\times(\nabla\times u)
\]

reduces the nonlinearity to ∇(|u|²/2), since curl u=N u. It is canceled exactly by ∇p; the time derivative equals νΔu. In particular the convective term is **nonzero**: at the origin it equals A² e^(−2νN²t) N(1,1,1).

This ABC field has genuine 3D spatial dependence and nonconstant pressure. It remains a Beltrami solution, so the convective term is a pure pressure gradient and the flow has no nonlinear mode-to-mode energy transfer. No claim of an active turbulent cascade follows from its nonzero advection.

The six exact Gaussian-rational Fourier coefficients (positive and negative modes on the x-, y-, and z-axes) permit exact convolution of both (u·∇)u and ∇p. The independent [Fourier verifier](../../scripts/bsar13_abc_pressure.py) checks their cancellation at every frequency, nonzero advection at the origin, divergence and curl identities, as well as Parseval sums.

## Vorticity direction and half-maximum core

The vorticity is ω=N u. The high-vorticity core is the set |U_N(x)|≥max|U_N|/2, independent of t and amplitude. At the origin U_N=(1,1,1), while everywhere |U_N|≤2√3. Hence the origin is in the core. Translating by (π/N,π/N,π/N) flips every sine and cosine, giving U_N=−(1,1,1), another core point.

The two points are a distance √3π/N apart on the torus and have opposite directions. Therefore

\[
K_\xi\ge\frac{4N}{\sqrt3\pi}>\frac N2.
\]

Globally the gradient Frobenius norm is at most √6N<3N. Every point in the high core obeys |U_N|≥√3/2. Normalizing two vectors with that minimum length shows

\[
|\xi(x)-\xi(y)|\le
\min(2,12N\,d_{\mathbb T^3}(x,y)).
\]

Consequently,

\[
\boxed{\frac N2\le K_\xi\le24N.}
\]

The endpoint-bound argument uses only values at core points; it avoids defining the vorticity direction at any possible zeros elsewhere in the domain. The derivative and geodesic distance estimates are mathematical steps documented here rather than Lean-kernel theorems.

## Critical homogeneous Sobolev normalization and the cone cost

The spatial-average squared L² norm of U_N equals 3, and the mean enstrophy of u is

\[
D(t)=3A^2N^2e^{-2\nu N^2t}.
\]

Choose N=m⁴, A=m^(−q), s=q/4, with q∈{0,1,2,3,4}, m≥2. Then

\[
\|u(0)\|_{\dot H^s,\mathrm{avg}}^2
=3A^2N^{2s}=3
\]

exactly for all m in a fixed q cohort.

Let x=2νN²T. The cone integral satisfies

\[
\frac{3A^2N}{4\nu}(1-e^{-x})
\le
\int_0^T K_\xi(t)D(t)\,dt
\le
\frac{36A^2N}{\nu}.
\]

For x≥1, using 1−e^(−x)≥x/(1+x)≥1/2 gives the bracket

\[
\boxed{
\frac{3m^{4-2q}}{8\nu}
\le
\int_0^T K_\xi D\,dt
\le
\frac{36m^{4-2q}}{\nu}.
}
\]

The threshold s=1/2 persists in this **exact ABC Beltrami family** with active pressure-balanced advection: s<1/2 allows arbitrarily large cone cost with fixed initial homogeneous H^s norm, s=1/2 keeps it order 1/ν, and s>1/2 yields decay. This is a family-specific scaling result. It neither proves a global H^(1/2) regularity theorem nor rules out stronger geometry/initial-data-dependent estimates.

At any fixed positive start time τ<T,

\[
\int_\tau^T K_\xi D\,dt
\le
\frac{36A^2N}{\nu(1+2\nu N^2\tau)}
\le
\frac{18}{\nu^2\tau}
\]

for these modes. Thus the high-frequency blow-up of the full-time cone budget comes from the shrinking initial layer.

## Reproduction and limitations

The [exact checker](../../scripts/bsar13_abc_pressure.py) and [tests](../../tests/test_bsar13_abc_pressure.py) use standard-library Fraction and Gaussian-rational Fourier coefficients with no floating-point PDE derivatives. It creates 360 deterministic cases, including positive-start-time bounds and SHA-256 integrity receipts.

    python -m unittest discover -s tests -p 'test_bsar13_abc_pressure.py' -v
    python scripts/bsar13_abc_pressure.py generate --out /tmp/bsar13
    python scripts/bsar13_abc_pressure.py audit --out /tmp/bsar13

The exact algebraic claims are checked programmatically; the trigonometric, exponential, gradient, and high-core geometry inequalities are derived in the note. The source does not purport to prove general 3D Navier–Stokes regularity in Lean.

The outstanding analytic target remains a PDE-derived bound for the dimensionless sum of BSA-R window costs ΣI_m/M, as tracked in [MathCan BSAR-09 issue #186](https://github.com/patrickdugan/MathCan/issues/186). Pressure-balanced ABC flows remain a special class: a future test of **non-gradient convective interaction and genuine vorticity stretching** needs additional mathematical structure.

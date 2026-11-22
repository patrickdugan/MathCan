# BSAR-12: two-mode exact shear, nonzero direction tension and cone-cost scaling

This is the registered [BSAR-12 target](https://github.com/patrickdugan/MathCan/issues/199), following [BSAR-10](https://github.com/patrickdugan/MathCan/pull/194) and [BSAR-11](https://github.com/patrickdugan/MathCan/pull/197). The original cone quantity comes from [BSA-R's Round 6 specification](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/navier_stokes/ROUND6_COLLABORATOR_SPEC.md).

## A genuine two-frequency Navier–Stokes flow

On the flat periodic three-torus, write h_n(z)=(cos(nz),sin(nz),0). For n a positive integer, a>0, b=a/8, and viscosity ν>0, define

\[
u(z,t)=a_t h_n(z)+b_t h_{2n}(z),\quad
a_t=a e^{-\nu n^2t},\quad b_t=b e^{-4\nu n^2t}.
\]

The pressure is zero. The velocity has zero vertical component and depends only on z, so its nonlinear term (u·∇)u vanishes identically. Each Fourier mode independently solves the heat equation. The spatial mean is zero, and this is an **exact, globally smooth, unforced Navier–Stokes solution**. Because the frequencies have distinct Laplacian eigenvalues, the combined field is not a single Beltrami eigenmode.

The vorticity is

\[
\omega(z,t)=-n a_t h_n(z)-2n b_t h_{2n}(z).
\]

Its spatially averaged enstrophy is

\[
D(t)=n^2a^2e^{-2\nu n^2t}+4n^2b^2e^{-8\nu n^2t}.
\]

The [source-aligned Gaussian-rational Fourier verifier](../../scripts/bsar12_two_mode_helical.py) checks all four Fourier coefficients, zero divergence, curl eigenrelations, the two distinct heat eigenvalues, zero convective convolution and Parseval energy/enstrophy.

## The full domain remains in the high-vorticity core

Let r(t)=2b_t/a_t=(1/4)e^{-3νn²t}. Then 0<r(t)≤1/4 and

\[
n a_t(1-r(t))\le|\omega(z,t)|\le n a_t(1+r(t)).
\]

Hence

\[
\frac{\min_z|\omega(z,t)|}{\max_z|\omega(z,t)|}
\ge\frac{1-r(t)}{1+r(t)}\ge\frac35>\frac12.
\]

Every point remains inside the usual half-maximum high-vorticity core, and the normalized direction field is well-defined everywhere for every finite time.

At z=0 and z=π/n the vorticity directions point exactly opposite ways, since 0<r<1. The torus distance is π/n, yielding

\[
K_\xi(t)\ge4n/\pi\ge n.
\]

Differentiating and normalizing the two-mode field gives |∂_z ξ|≤n(1+2r)/(1-r)≤2n. Thus for geodesic separation d, |ξ(x)-ξ(y)|≤min(2,2nd), and

\[
\boxed{n\le K_\xi(t)\le4n.}
\]

These geometric inequalities use elementary calculus and periodic distance geometry; the exact-rational verifier checks their coefficient constraints and resulting algebraic receipts.

## A nonzero harmonic-map tension witness

The direction, up to a constant negative sign, is the phase of

\[
F(\theta)=e^{i\theta}+r e^{2i\theta},\qquad\theta=nz.
\]

For the direction angle φ(θ),

\[
\varphi''(\theta)=
-\frac{r(1-r^2)\sin\theta}{(1+2r\cos\theta+r^2)^2}.
\]

Writing ξ=(cos φ,sin φ,0) up to sign gives

\[
\partial_{zz}\xi+|\partial_z\xi|^2\xi
=n^2\varphi''(\theta)\,(-\sin\varphi,\cos\varphi,0),
\]

so the covariant S² harmonic-map tension is **nonzero** whenever 0<r<1 and sinθ≠0.

At t=0, r=1/4, θ=π/2, the exact magnitude is

\[
\left|\Delta\xi+|\nabla\xi|^2\xi\right|
=\frac{60}{289}n^2.
\]

The verifier computes the derivative identities from exact Gaussian-rational values F,F′,F″ and checks the 60/289 ratio. The differential identity itself is derived in the note, rather than claimed as a Lean formalization.

This addresses a specific limitation of BSAR-10: the cone-cost obstruction persists when the direction has a nonzero harmonic-map tension and two distinct active frequencies.

## Sobolev-normalized critical scaling

Choose m≥2, q∈{0,1,2,3,4}, with

\[
n=m^4,\qquad a=m^{-q},\qquad s=q/4,\qquad b=a/8.
\]

The initial squared homogeneous Sobolev seminorm under normalized Fourier averages is

\[
\|u(0)\|_{\dot H^s}^2
=a^2 n^{2s}+b^2(2n)^{2s}
=1+\frac{2^{2s}}{64}
\in\left[\frac{65}{64},\frac{17}{16}\right].
\]

For odd q, 2^(2s) is irrational. The exact-rational verifier encloses it using squared inequalities: 7/5≤√2≤3/2 and 14/5≤2√2≤3. It never substitutes a floating-point approximation. For even q the value is exact in rational arithmetic.

Let J(0,T)=∫₀ᵀ Kξ(t)D(t)dt and x=2νn²T. Since b=a/8 and e^(−8νn²t)≤e^(−2νn²t),

\[
\frac{a^2n}{2\nu}(1-e^{-x})
\le J(0,T)
\le\frac{17a^2n}{8\nu}.
\]

When x≥1, exponential convexity gives 1−e^(−x)≥x/(1+x)≥1/2, so

\[
\boxed{
\frac{m^{4-2q}}{4\nu}\le J(0,T)
\le\frac{17m^{4-2q}}{8\nu}.}
\]

The high-frequency threshold for this explicit **two-frequency** family remains s=1/2. The q=0 and q=1 families have unbounded cone cost at fixed Sobolev norm; q=2 stays order 1/ν; q=3,4 decay. This is a family-specific scaling diagnostic, not a universal Navier–Stokes criterion. The index s=1/2 also occurs in classical Fujita–Kato critical-velocity results; those concern a distinct general PDE theory.

For fixed 0<τ<T, the positive-start-time integral obeys

\[
J(\tau,T)\le\frac{17a^2n}{8\nu}e^{-2\nu n^2\tau}
\le\frac{17a^2n}{8\nu(1+2\nu n^2\tau)}
\le\frac{17}{16\nu^2\tau}.
\]

This is uniform in n for this family and tends to zero with high-frequency n at any fixed positive τ.

## Verification boundary

The [dedicated BSAR-12 CI](../../.github/workflows/bsar12-two-mode.yml) uses exact Gaussian-rational Fourier coefficients and standard-library Fraction arithmetic, verifies the phase-acceleration witness, replays all 360 parameter cases with SHA-256 custody, and checks source revision provenance.

It does not run a fluid simulation, train a model, or formally encode the full NSE in Lean. The trigonometric, exponential and time-differentiation arguments are displayed as ordinary mathematical proofs alongside the exact algebraic receipts.

The remaining step in [MathCan BSAR-09 issue #186](https://github.com/patrickdugan/MathCan/issues/186) is a rigorous PDE-derived budget for the dimensionless window sum Σ(I_m/M), with explicit dependence on initial data and direction regularity. A two-mode exact shear does not establish such a bound for general flows.

# BSAR-11: critical Sobolev scaling in exact helical Navier–Stokes modes

This extends the [BSAR-10 helical-flow calculation](https://github.com/patrickdugan/MathCan/pull/194) and the [BSAR-09R conditional real Grönwall theorem](https://github.com/patrickdugan/MathCan/pull/190). We test which initial homogeneous Sobolev norm prevents the energy-only cone-budget obstruction for an explicit family of smooth flows.

The direction-cone quantity comes from [BSA-R's Round 6 collaborator specification](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/navier_stokes/ROUND6_COLLABORATOR_SPEC.md).

## Amplitude-normalized helical modes

On the flat torus (R/2πZ)^3 with volume-normalized spatial averages, choose integer m>=2, q in {0,1,2,3,4}, viscosity ν>0, and

\[
N=m^4,\qquad A=m^{-q},\qquad s=q/4.
\]

Then the exact smooth unforced, zero-pressure Navier–Stokes solution is

\[
u_{m,q}(x,y,z,t)=A e^{-\nu N^2t}(\cos Nz,\sin Nz,0).
\]

The initial squared homogeneous Sobolev seminorm (Fourier multiplier |k|^(2s)) is

\[
\|u_{m,q}(0)\|_{\dot H^s,\mathrm{avg}}^2=A^2N^{2s}
=m^{-2q}(m^4)^{q/2}=1.
\]

For each fixed s in the table below, this norm is independent of m. The initial kinetic energy density and enstrophy density are respectively A^2/2 and A^2 N^2. The nonlinear advection vanishes because u has zero vertical component and depends only on z, while the Laplacian equals -N^2 u.

Its nonzero vorticity is ω=-Nu, so the normalized direction is ξ=-(cos Nz,sin Nz,0), independent of A and finite t. The high-vorticity core is the entire torus at each finite time.

## Exact cone-cost scaling

For shortest vertical separation h, the direction difference satisfies

\[
|\xi(z+h)-\xi(z)|^2=2(1-\cos Nh).
\]

The elementary cosine Lipschitz bound |1-cos θ|≤|θ| gives Kξ(t)≤2N. Choosing h=π/N gives opposite directions, and hence Kξ(t)≥4N/π≥N. Thus the cone seminorm is time-independent and trapped between N and 2N.

The spatial-average enstrophy is

\[
D(t)=A^2N^2e^{-2\nu N^2t}.
\]

For the complete cone integral J(0,T)=∫₀ᵀ Kξ(t)D(t)dt this yields

\[
\frac{A^2N}{2\nu}(1-e^{-2\nu N^2T})
\le J(0,T)\le
\frac{A^2N}{\nu}(1-e^{-2\nu N^2T}).
\]

When 2νN²T≥1, use e^x≥1+x to obtain

\[
\boxed{\frac{m^{4-2q}}{4\nu}\le J(0,T)\le\frac{m^{4-2q}}{\nu}.}
\]

The exponent 4-2q equals 4(1-2s). This is the exact frequency scaling for this particular single-mode family while the initial homogeneous H^s seminorm remains one.

| Sobolev s | q | Cone-integral scale for fixed ν,T>0 and large m |
|---|---:|---|
| 0 | 0 | m⁴/ν, unbounded |
| 1/4 | 1 | m²/ν, unbounded |
| 1/2 | 2 | 1/ν, bounded above and below |
| 3/4 | 3 | m⁻²/ν, decays |
| 1 | 4 | m⁻⁴/ν, decays |

In particular, a uniform bound on the proposed cone integral based only on the homogeneous H^(1/4) seminorm, viscosity, T and domain fails across this family. For an arbitrary real exponent s<1/2, the same paper-level scaling follows with A=N^(-s), giving J on the order of N^(1-2s)/ν.

For s=1/2 the cone integral is bounded for these helical modes. This is **not** a global H^(1/2) regularity criterion for arbitrary 3D Navier–Stokes solutions.

## Literature context and interpretation

The index s=1/2 is already familiar as the scale-critical homogeneous Sobolev exponent in the three-dimensional Navier–Stokes theory. The [Fujita–Kato small-data result and its later formulations](https://link.springer.com/article/10.1007/s00205-026-02171-x) use this critical initial-velocity space. The direction-of-vorticity regularity literature, beginning with [Constantin–Fefferman (1993)](https://iumj.org/article/3627/) and including [Beirão da Veiga's 2019 discussion](https://www.aimsciences.org/article/doi/10.3934/dcdss.2019014), also emphasizes a half-Hölder direction threshold. The H^(1/2) velocity norm and the C^(1/2) direction-coherence condition are distinct objects with different assumptions.

BSAR-11 establishes the s=1/2 threshold only for the explicitly constructed one-frequency shear/Beltrami family and for the specific cone-energy integral in BSA-R. It does not establish a novel universal critical regularity criterion or improve the Fujita–Kato theorem.

## The positive-time cutoff

Fix 0<τ<T. The integral from τ to T satisfies

\[
\begin{aligned}
J(\tau,T)
&\le\frac{A^2N}{\nu}(e^{-2\nu N^2\tau}-e^{-2\nu N^2T})\\
&\le\frac{A^2N}{\nu(1+2\nu N^2\tau)}
\le\frac1{2\nu^2\tau}.
\end{aligned}
\]

The second step uses e^x≥1+x, and the last uses A≤1 and N≥1. This provides a frequency-uniform bound for the specified family at every fixed positive τ. Its rational upper envelope tends to zero as N increases. A comparable energy-only positive-time theorem for **general** Navier–Stokes solutions is not established here.

The large full-time integral is therefore concentrated in a rapidly shrinking initial layer. Its divergence across initial data does not imply any individual flow blows up.

## Vanishing tension with growing gradients

These directions satisfy

\[
|\nabla\xi|^2=N^2,\qquad
\Delta\xi=-N^2\xi,\qquad
\Delta\xi+|\nabla\xi|^2\xi=0.
\]

Each mode is a nonconstant harmonic map into the equator of S², with zero covariant tension despite arbitrarily large gradients. The Python exact Fourier audit verifies pointwise unit speed and gradient magnitude, from which the tension identity follows by analytic differentiation.

## Evidence boundary and reproduction

The standard-library [Gaussian-rational/Fraction audit](../../scripts/bsar11_sobolev_critical_audit.py) checks exact Fourier modes, divergence, curl, nonlinear cancellation, normalized H^s multipliers, and rational cone-cost bounds. Its 360-case deterministic corpus varies 12 frequency bases, five Sobolev exponents, three viscosities and two horizons, with a SHA-256 source receipt.

    python -m unittest discover -s tests -p 'test_bsar11_sobolev_critical_audit.py' -v
    python scripts/bsar11_sobolev_critical_audit.py generate --out /tmp/bsar11
    python scripts/bsar11_sobolev_critical_audit.py audit --out /tmp/bsar11

The geometric cone bounds and exponential comparison are derived in the note, with exact rational checks supplied by the program. They are not Lean-kernel formalizations of the full Navier–Stokes equations.

The outstanding task in [MathCan BSAR-09 issue #186](https://github.com/patrickdugan/MathCan/issues/186) is an actual PDE-derived bound on the dimensionless window sum Σ(I_m/M), with its dependence on initial regularity, geometric coherence, and the time interval made explicit.

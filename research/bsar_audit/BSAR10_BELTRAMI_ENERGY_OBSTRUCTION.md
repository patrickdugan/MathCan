# BSAR-10: an exact helical-flow obstruction to an energy-only cone budget

**Question.** Does the Leray kinetic-energy inequality, by itself, control the proposed high-vorticity direction-cone integral

\[
J(T)=\int_0^T K_\xi(t)D(t)\,dt,\qquad
K_\xi(t)=\sup_{x\ne y\text{ in high-vorticity core}}
\frac{|\xi(x,t)-\xi(y,t)|^2}{d_{\mathbb T^3}(x,y)}?
\]

This is the quantity proposed in [BSA-R's Round 6 collaborator specification](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/navier_stokes/ROUND6_COLLABORATOR_SPEC.md). MathCan [BSAR-09R](https://github.com/patrickdugan/MathCan/pull/190) established a **conditional** real Grönwall/product estimate when a uniform dimensionless window budget is already supplied. BSAR-10 examines a narrower missing implication, from kinetic energy to the cone integral.

## An exact family of smooth unforced Navier–Stokes solutions

Work on the flat torus \(\mathbb T^3=(\mathbb R/2\pi\mathbb Z)^3\), with spatial averages normalized by its volume \(V=(2\pi)^3\). Fix \(\nu>0\), \(T>0\), and an integer frequency \(N\ge1\). Define

\[
u_N(x,y,z,t)
=e^{-\nu N^2t}\bigl(\cos Nz,\sin Nz,0\bigr),\qquad p_N=0.
\]

Direct differentiation establishes, for every finite \(t\ge0\),

\[
\nabla\cdot u_N=0,\qquad
(u_N\cdot\nabla)u_N=0,\qquad
\Delta u_N=-N^2u_N,\qquad
\partial_tu_N=-\nu N^2u_N.
\]

Thus \(\partial_tu_N+(u_N\cdot\nabla)u_N+\nabla p_N=\nu\Delta u_N\) **exactly**. The spatial mean is zero, and each solution is smooth at all times. This is a simple decaying Beltrami/Trkal mode, within a classical family of exact helical Navier–Stokes solutions. See the [review of helical flows](https://doi.org/10.1134/S0081543823040156).

Its vorticity and direction are

\[
\omega_N=\nabla\times u_N=-Nu_N,\quad
\Omega_N=|\omega_N|=Ne^{-\nu N^2t},\quad
\xi_N=-(\cos Nz,\sin Nz,0).
\]

The entire torus is in the high-vorticity core \(\{\Omega\ge\frac12\Omega_{\max}\}\) for every finite time. The direction is well-defined everywhere. Hence the threshold and the zero-vorticity-set convention do not affect this construction.

## Fixed energy, growing cone integral

The spatially averaged initial kinetic energy is identical across all frequencies:

\[
E_N(0)=\frac1{2V}\int_{\mathbb T^3}|u_N(x,0)|^2\,dx=\frac12.
\]

The enstrophy density is

\[
D_N(t)=\frac1V\int|\omega_N|^2\,dx
=N^2e^{-2\nu N^2t}.
\]

The exact viscous energy budget satisfies

\[
\nu\int_0^T D_N(t)\,dt
=\frac{1-e^{-2\nu N^2T}}2
\le\frac12=E_N(0).
\]

Choose points \(x=(0,0,0)\) and \(y=(0,0,\pi/N)\). Their torus distance is \(\pi/N\), while their vorticity directions are antiparallel. Therefore

\[
K_{\xi_N}(t)\ge\frac4{\pi/N}=\frac{4N}{\pi}\ge N
\]

independently of time. Combining this with the exact enstrophy integral gives

\[
\begin{aligned}
J_N(T)
&\ge \frac{4N}{\pi}\int_0^TN^2e^{-2\nu N^2t}\,dt\\
&=\frac{2N}{\pi\nu}\left(1-e^{-2\nu N^2T}\right).
\end{aligned}
\]

For all \(N\) with \(x_N:=2\nu N^2T\ge1\), the elementary bound \(e^{x_N}\ge1+x_N\) yields

\[
1-e^{-x_N}\ge\frac{x_N}{1+x_N}\ge\frac12.
\]

Consequently,

\[
\boxed{J_N(T)\ge\frac{N}{4\nu}\longrightarrow\infty}
\]

as \(N\to\infty\), even though \(E_N(0)=1/2\) for every member of the family. The coefficient \(1/4\) is a deliberately conservative rational lower bound, obtained by using \(K_\xi\ge N\).

**Precise conclusion:** There is no uniform bound for \(J(T)\) that depends *only* on \(E(0)\), \(\nu\), \(T\), and the fixed torus geometry, over all smooth zero-mean unforced Navier–Stokes initial data. Every individual \(u_N\) remains globally regular, and every individual \(J_N(T)\) is finite. A bound depending on stronger initial data, or an estimate starting at a fixed positive time, is not excluded by this example. It is also not a blow-up example and does not settle global regularity.

## The direction PDE explains why curvature tension alone is insufficient

Here \(\xi_N\) winds around the equator of \(S^2\). It satisfies

\[
|\nabla\xi_N|^2=N^2,\qquad
\Delta\xi_N=-N^2\xi_N,\qquad
\Delta\xi_N+|\nabla\xi_N|^2\xi_N=0.
\]

The last expression is the **covariant harmonic-map tension**, which vanishes exactly, despite the unbounded spatial direction gradient. The vorticity stretching \(\omega\cdot S\omega\) also vanishes for this Beltrami mode.

In the scalar-amplitude equation, the direction-curvature sink equals \(-\nu N^2\Omega_N\), precisely accounting for \(\partial_t\Omega_N=-\nu N^2\Omega_N\). This example demonstrates that a coercive estimate for \(K_\xi\) cannot follow merely from the norm of harmonic-map tension. Such an estimate would need to account for the direction's harmonic maps, and possibly an initial-direction norm or stronger geometric structure.

The original direction-depletion literature emphasizes the geometric kernel that vanishes for both parallel and antiparallel vorticity orientations; see [Constantin–Fefferman (1993)](https://iumj.org/article/3627/) and [Beirão da Veiga–Berselli (2002)](https://arpi.unipi.it/handle/11568/178650). The BSA-R quantity \(|\xi(x)-\xi(y)|^2/|x-y|\) distinguishes antiparallel directions and therefore measures a stronger quantity than the sign-insensitive determinant in the stretching representation. Even the sign-insensitive quantity \(\sin^2\theta/|x-y|\) can grow linearly with \(N\) in this example, using \(\Delta z=\pi/(2N)\).

## Exact source-level verification

The [standard-library Python certificate](../../scripts/bsar10_beltrami_energy_audit.py) encodes the Fourier coefficients at modes \(k=(0,0,\pm N)\) as **Gaussian rational numbers**, with no floating-point PDE derivatives:

\[
\hat u_{+N}=(1/2,-i/2,0),\qquad
\hat u_{-N}=(1/2,+i/2,0).
\]

It checks Fourier divergence, the curl eigenrelation \(\nabla\times u=-Nu\), the Laplacian eigenvalue \(-N^2\), and every convolution term in \((u\cdot\nabla)u\). Parseval yields normalized initial kinetic energy and enstrophy exactly. A rational lower receipt for each \((N,\nu,T)\) checks

\[
J_N(T)\ge\frac{N}{2\nu}\frac{x_N}{1+x_N},
\qquad x_N=2\nu N^2T.
\]

The geometric \(K_\xi\) lower bound, time integration, and exponential convexity are mathematical facts derived in this note; the Python program does not prove these analytic facts in a theorem prover. It supplies a reproducible **exact Fourier and rational arithmetic audit**, with all assumptions stated.

Reproduce with

```sh
python -m unittest discover -s tests -p 'test_bsar10_beltrami_energy_audit.py' -v
python scripts/bsar10_beltrami_energy_audit.py generate --out /tmp/bsar10
python scripts/bsar10_beltrami_energy_audit.py audit --out /tmp/bsar10
```

The deterministic corpus contains 414 parameter cases across 69 frequencies, three viscosities and two horizons. SHA-256 manifests bind the records.

## Research consequences for BSAR-09R

The remaining valid path needs a budget \(B\) that either depends on stronger initial regularity or comes from a genuinely new inequality at the PDE level. An assumption like

\[
\int_0^T K_\xi(t)D(t)\,dt\le C(\nu,T, E(0))
\]

cannot hold uniformly for the source's cone definition. A route using \(\sup_{t\in[0,T]}K_\xi(t)\), high-order Sobolev norms, or additional coherence hypotheses must specify the dependence and its behavior near a hypothetical singular time.

A stronger next test would seek a *single fixed initial datum* and uniform-in-time estimates up to its maximal existence time. The frequency family does not address that problem. The recent BSAR-09R product bound is an algebraic consequence of an assumed dimensionless window budget; a PDE theorem must still provide that budget without treating enstrophy or initial kinetic energy as an interchangeable resource.

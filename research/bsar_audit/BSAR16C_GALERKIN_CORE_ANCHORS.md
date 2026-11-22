# BSAR-16C: time-uniform, rational vorticity-core anchor witnesses for exact Galerkin

Parent [BSAR-16 #213](https://github.com/patrickdugan/MathCan/issues/213). Dependencies: exact BSAR-14 source, merged [BSAR-16A #214](https://github.com/patrickdugan/MathCan/pull/214), and [BSAR-16B #216](https://github.com/patrickdugan/MathCan/pull/216) rational dense-path residual and gradient bounds.

**Evidence boundary:** This stage certifies anchor-point membership in the **continuum half-maximum vorticity core of the exact finite Fourier–Galerkin ODE solution** throughout \(0\le t\le T=3/250\). The continuous spatial maximum is bounded analytically. The calculation requires no sampling grid, FFT, RK4, floating-point rounding, or global-in-time PDE regularity assumption. It does **not** establish the same anchors for the infinite-dimensional Navier–Stokes solution, and it does not certify the BSAR-15 floating-point RK4 trajectory.

## Exact source geometry and envelopes

For frequency \(N=1,2\), amplitude \(A=1\) and phase \(\sigma=\pm1\), the eight Gaussian-rational coefficients from BSAR-14 give the source-pinned anchors

\[
x_0=(0,0,\pi/(2N)),\qquad x_1=(\pi/N,0,\pi/(2N)),
\]

with exact initial vorticities

\[
\omega_0(x_0)=(0,-N,-5\sigma N),\qquad
\omega_0(x_1)=(0,-N,+5\sigma N).
\]

Both initial norms equal \(\sqrt{26}N\). Their squared normalized direction difference is \(50/13\), while the global continuum bound on the original field is \(\|\omega_0\|_\infty\le\sqrt{65}N\). The shortest periodic geodesic between anchors is \(\pi/N\).

For the exact initial Fourier field the stronger weighted \(\ell^1\) calculation gives

\[
G_0=\sum_k |k|\,|\widehat u_0(k)|=(1+2+5+1)N=9N.
\]

The four contributions correspond exactly to the four conjugate source mode pairs. All quantities are independent of the phase sign.

## Transfer the rational Galerkin error into pointwise vorticity

Let \(v_K(t)\) solve the *exact* finite Galerkin ODE from the BSAR-14 datum and \(p(t)=a_0+t a_1+t^2 a_2\) be the degree-two rational reference from BSAR-16B.

The BSAR-16B analysis supplies, for all \(0\le t\le T\),

\[
\|v_K(t)-p(t)\|_2\le Y_T,\qquad
\|\nabla v_K(t)\|_\infty\le G_0+G_1T+G_2T^2+C_K Y_T=:G_{\mathrm{all}},
\]

where \(C_K=\sqrt{K(K+1)(2K+1)^3}\). Its archived \(G_{\mathrm{all}}\) is rounded **upward** to a rational multiple of \(10^{-9}\). Since \(G_0=9N\) holds exactly,

\[
\begin{aligned}
|\omega_{v_K}(x,t)-\omega_0(x)|
&\le |\nabla\times(p(t)-a_0)|+|\nabla\times(v_K(t)-p(t))|\\
&\le G_1T+G_2T^2+C_KY_T\\
&\le \underbrace{G_{\mathrm{all}}-9N}_{\varepsilon}.
\end{aligned}
\]

This is a uniform bound **over the continuous torus and every time in the interval**. It does not rely on a finite spatial sampling maximum.

The continuous vorticity maximum and both anchor lower norms then satisfy

\[
\|\omega_{v_K}(t)\|_\infty
\le\sqrt{65}N+\varepsilon,\qquad
|\omega_{v_K}(x_i,t)|\ge\sqrt{26}N-\varepsilon.
\]

Consequently the original anchor pair remains in the actual Galerkin half-maximum core whenever

\[
\boxed{m_{\mathrm{core}}=
(2\sqrt{26}-\sqrt{65})N-3\varepsilon>0.}
\]

The verifier uses a rational **lower** square-root bound for \(\sqrt{26}\) and an **upper** bound for \(\sqrt{65}\), always directing the final core margin downward.

## Direction-cone witness

Provided the core margin is positive, both normalized vorticities \(\xi_i(t)=\omega_{v_K}(x_i,t)/|\omega_{v_K}(x_i,t)|\) are defined. The normalized-vector perturbation inequality gives

\[
|\xi_i(t)-\xi_i(0)|
\le\frac{2\varepsilon}{\sqrt{26}N-\varepsilon}.
\]

Thus the two anchor directions remain separated by at least

\[
D_{\min}=\sqrt{50/13}-
\frac{4\varepsilon}{\sqrt{26}N-\varepsilon}.
\]

When \(D_{\min}>0\), the cone quotient over the true continuous Galerkin core obeys

\[
\boxed{
K_{\xi,K}(t)\ge\frac{N}{\pi}D_{\min}^2
\ge\frac{7N}{22}D_{\min}^2>0,
\qquad 0\le t\le T,
}
\]

using \(\pi<22/7\). The implementation rounds \(\sqrt{50/13}\) downward, the denominator \(\sqrt{26}N-\varepsilon\) downward, and the final cone witness downward to a rational multiple of \(10^{-9}\). A failed sign or near-zero denominator produces an explicitly uncertified row.

## Registered twelve-case results

The following conservative figures were independently evaluated from BSAR-16B's first rational receipt archive. Rows take the least favorable phase \(\sigma\) at the indicated \(N,M\). Figures below are rounded outward for display; exact rational certificates reside in the dedicated BSAR-16C archive.

| Initial N | Grid M | Sup vorticity perturbation \(\varepsilon\) upper | Half-core margin lower | Cone \(K_{\xi,K}\) lower |
|---:|---:|---:|---:|---:|
| 1 | 16 | 0.256044 | 1.3676 | 0.9740 |
| 1 | 24 | 0.257398 | 1.3635 | 0.9727 |
| 1 | 32 | 0.260613 | 1.3539 | 0.9696 |
| 2 | 16 | 1.123265 | 0.9017 | 1.3677 |
| 2 | 24 | 1.143500 | 0.8410 | 1.3490 |
| 2 | 32 | 1.215896 | 0.6238 | 1.2826 |

The least margin stays above 0.6238 and the smallest certified cone lower bound stays above 0.9696. The two source anchor points are therefore eligible as **continuum-core witnesses for the exact Galerkin trigonometric solution across the entire registered interval**, including all \(\sigma=\pm1\) phases. These results go beyond the earlier BSAR-15 *floating* anchor-envelope candidates because they enclose the exact Galerkin ODE path using rational defect and energy inequalities.

The pointwise perturbation used here is computed from a **finite-dimensional Fourier inverse estimate**. An analogous pointwise vorticity estimate for the difference between the Galerkin solution and the infinite-dimensional NSE solution would require higher Sobolev regularity control. BSAR-16B's conditional \(L^2\) solution-error bound alone cannot justify transfer of these anchors to the true PDE.

## Reproduce

The dedicated CI uses standard-library Python 3.11 only:

~~~sh
python -m unittest experiments.bsar16.test_core_intervals -v
python -m experiments.bsar16.core_intervals generate --out /tmp/bsar16c
python -m experiments.bsar16.core_intervals audit --out /tmp/bsar16c
~~~

It independently checks the original BSAR-14 exact anchor values, the \(G_0=9N\) weighted norm identity, outward and inward rational sqrt controls, the half-core positivity gate, a negative-control perturbation large enough to invalidate the gate, and reproducibility of the twelve-case JSON receipts with SHA-256.

**Open BSAR-16 gates:** validate the original NumPy/RK4 dense numerical path with FFT roundoff, obtain a derivative-norm or high-Sobolev full-PDE error bound strong enough to preserve anchor-core membership for the true NSE solution, and establish quantitative sign-persistence durations from transfer derivative bounds. The PDE-derived dimensionless-window budget in [BSAR-09 #186](https://github.com/patrickdugan/MathCan/issues/186) remains open.

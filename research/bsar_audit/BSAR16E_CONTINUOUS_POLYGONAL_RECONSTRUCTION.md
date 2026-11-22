# BSAR-16E: continuous-time certified polygonal reconstruction of Fourier RK4 snapshots

Parent: [BSAR-16 #213](https://github.com/patrickdugan/MathCan/issues/213). The input is the [BSAR-16D #220](https://github.com/patrickdugan/MathCan/pull/220) a posteriori binary64 Fourier time-node certificate, whose first dedicated all-node archive has canonical JSON SHA-256:

    9ef44ff668bb98e4c0d8ac925e13842ed10f3fa4230fd7ede2dd6740837c8e58

**Scope:** a rigorously enclosed, explicitly defined continuous-time **piecewise-linear reconstruction** of the original saved NumPy FFT/RK4 Fourier states. The linear interpolation acts on the real, Leray-projected mathematical Fourier fields associated with the observed binary64 tensors. It is a post-hoc interpolant and is **not** a certificate for an RK4 internal dense-output formula or for unobserved FFT stages. The comparison to the exact Galerkin ODE rests on BSAR-16B's rational Taylor/energy majorant.

## Exact interpolation identity

Let \(p(t)=a_0+a_1 t+a_2 t^2\) be the BSAR-16B Gaussian-rational degree-two reference. For a time interval \([t_j,t_{j+1}]\) with \(h=t_{j+1}-t_j\), put \(\theta=(t-t_j)/h\in[0,1]\). The exact Fourier-polynomial identity is

\[
(1-\theta)p(t_j)+\theta p(t_{j+1})-p(t)
=\theta(1-\theta)h^2 a_2.
\]

Since \(0\le\theta(1-\theta)\le1/4\), it follows that

\[
\sup_{t_j\le t\le t_{j+1}}
\left\|(1-\theta)p(t_j)+\theta p(t_{j+1})-p(t)\right\|_2
\le\frac{h^2}{4}\|a_2\|_2.
\]

The verifier independently checks this identity with exact Gaussian-rational Fourier arithmetic at representative interior points. The coefficient norm is rounded outward using BSAR-16B's integer-square-root helper.

## Continuous-time reconstruction of the numerical coefficients

Let \(H_j\) be the full stored binary64 Fourier state produced by the original BSAR-15 solver at nominal time \(t_j\), and define its exact mathematical real, mean-zero, solenoidal projection \(W_j=\mathbb P P_{\mathrm{real}}H_j\). The operators are \(L^2\) contractions and fix each rational reference state \(p(t_j)\).

The BSAR-16D exact binary64 rational audit supplies

\[
D_j\ge\|H_j-p(t_j)\|_2,
\qquad \|W_j-p(t_j)\|_2\le D_j.
\]

Construct the **polygonal reconstructed Fourier field**

\[
W_{\mathrm{lin}}(t):=(1-\theta)W_j+\theta W_{j+1},
\qquad t\in[t_j,t_{j+1}].
\]

By convexity of the Fourier \(L^2\) norm and the exact quadratic interpolation remainder,

\[
\boxed{
\sup_{t\in[t_j,t_{j+1}]}
\|W_{\mathrm{lin}}(t)-p(t)\|_2
\le \max(D_j,D_{j+1})+\frac{h^2}{4}\|a_2\|_2
=:\Lambda_j.
}
\]

This bound includes the entire finite-precision error present in the two original binary64 endpoint tensors. Its derivation uses no FFT operation-error assumption or local RK4 truncation estimate.

## Comparison with the exact finite Galerkin solution

The BSAR-16B rational defect/energy argument gives the exact Galerkin solution \(v_K(t)\) a time-dependent error bound \(Y(t)\ge\|v_K(t)-p(t)\|_2\), where the underlying exponential is explicitly enclosed by a rational upper approximation.

Since the coefficient sums and their integrals entering \(Y\) are nonnegative, for all \(t\in[t_j,t_{j+1}]\) the same proof gives \(\|v_K(t)-p(t)\|_2\le Y(t_{j+1})\). Therefore

\[
\boxed{
\sup_{t\in[t_j,t_{j+1}]}
\|W_{\mathrm{lin}}(t)-v_K(t)\|_2
\le \Lambda_j+Y(t_{j+1}).
}
\]

Both terms are computed with exact rational operations and upward-rounded square roots. The first term is a certified discrepancy of the **original reported numerical coefficient arrays**, while the second is independent analytic error control for the rational reference.

## Vorticity anchors over continuous space and continuous time

For the source-pinned BSAR-14 pair at \(x_0=(0,0,\pi/(2N))\) and \(x_1=(\pi/N,0,\pi/(2N))\), the initial vorticity norms are \(\sqrt{26}N\), the global maximum has upper bound \(\sqrt{65}N\), and the initial normalized direction difference squared is \(50/13\).

Let \(C_K=\sqrt{K(K+1)(2K+1)^3}\) be the Fourier inverse-gradient constant, and \(G_i\ge\sum_k|k||\widehat a_{i,k}|\) be the exact rational coefficient upper envelopes. For every real time in the interval,

\[
\|\operatorname{curl}W_{\mathrm{lin}}(t)-\omega_0\|_\infty
\le G_1t_{j+1}+G_2t_{j+1}^2+C_K\Lambda_j
=:\varepsilon_j^{\mathrm{direct}}.
\]

An independent transferred estimate through \(v_K\) uses

\[
\varepsilon_j^{\mathrm{via\,G}}
=G_1t_{j+1}+G_2t_{j+1}^2
+C_KY(t_{j+1})+C_K(\Lambda_j+Y(t_{j+1})).
\]

When the rationally enclosed margin

\[
(2\sqrt{26}-\sqrt{65})N-3\varepsilon_j>0,
\]

both anchors lie in the **true continuous-spatial half-maximum vorticity core** of the polygonal Fourier reconstruction at *every time* in the interval. The normalized direction-separation lower bound

\[
\sqrt{50/13}-\frac{4\varepsilon_j}{\sqrt{26}N-\varepsilon_j}
\]

then supplies a positive cone quotient lower witness using \(N/\pi>7N/22\). Every square root and final margin is directed rationally toward a safe bound. If either gate fails, the archive reports an uncertified interval rather than substituting the original numerical sample statistic.

## Registered campaign and evidence limits

The exact BSAR-16D source contains 16 runs and 256 stored nodes across \(N=1,2\), phases \(\sigma=\pm1\), grids \(M=16,24,32\), standard rational time step \(1/1000\), and fine time step \(1/2000\) for \(M=32\). The polygonal reconstruction therefore has exactly **240 nonoverlapping time intervals**. A pin of the canonical BSAR-16D archive SHA-256 is supplied in dedicated CI, and each output run retains the corresponding full binary64 state-stream hash.

The audit checks the quadratic identity, all rational node labels and positive-error controls, the source and final campaign hashes, exact finite Fourier truncation dimensions, and a re-evaluation of every interval certificate. The dedicated workflow regenerates the BSAR-16D source archive from the original NumPy FFT/RK4 solver with pinned NumPy 2.3.5, requiring its SHA-256 to match the registered initial evidence before deriving the polygonal bounds.

Reproduce from MathCan with Python 3.11 and NumPy 2.3.5:

    python -m unittest experiments.bsar16.test_dense_interpolant -v
    python -m experiments.bsar16.float64_snapshots generate --out /tmp/bsar16d
    python -m experiments.bsar16.dense_interpolant generate --source /tmp/bsar16d --out /tmp/bsar16e
    python -m experiments.bsar16.dense_interpolant audit --source /tmp/bsar16d --out /tmp/bsar16e

**Remaining analytic boundary:** the continuous polygonal reconstruction is defined by interpolating *output coefficients* and is independently certified as an approximation to the exact finite Galerkin ODE. A rigorous defect for the *actual RK4 internal dense extension*, including FFT operation-level roundoff, would be a different theorem. The true infinite-dimensional Navier–Stokes vorticity core also requires a stronger derivative-norm PDE comparison and explicit local smoothness control. BSAR-09's uniform window-budget estimate remains open.

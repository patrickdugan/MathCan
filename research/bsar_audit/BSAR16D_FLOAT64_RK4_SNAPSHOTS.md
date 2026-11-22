# BSAR-16D: a posteriori binary64 RK4 Fourier snapshot certification

Parent: [BSAR-16 #213](https://github.com/patrickdugan/MathCan/issues/213). Dependencies: [BSAR-15 #210](https://github.com/patrickdugan/MathCan/pull/210) (original pinned NumPy FFT/RK4 campaign), [BSAR-16B #216](https://github.com/patrickdugan/MathCan/pull/216) (exact-rational Taylor reference and continuous Galerkin ODE error bound), and [BSAR-16C #217](https://github.com/patrickdugan/MathCan/pull/217) (exact Galerkin half-maximum core anchors).

## Mathematical scope

This stage certifies **actual stored Fourier coefficient arrays at all RK4 time nodes**, with every complex128 coefficient interpreted as its exact pair of binary64 rational numbers. It includes all the accumulated numerical error in the resulting coefficient array, independently of the FFT implementation, because it directly measures the rational discrepancy of those actual stored numbers against an independently constructed rational reference.

It does **not** provide an arithmetic-error estimate for an RK4 internal step or for an interpolated trajectory between nodes. NumPy FFT inverse-transform display values also have their own physical-grid rounding; this audit addresses the **mathematical trigonometric polynomial defined by stored Fourier numbers**. The independent rational reference uses analytic energy/Gronwall inequalities, verified computationally through Python rational arithmetic; these analytic inequalities have not been formalized in Lean.

For nominal rational time step \(h=1/1000\) or \(h=1/2000\), let \(H_j\) be the entire stored NumPy complex128 Fourier tensor after \(j\) steps of the unchanged BSAR-15 solver, and assign it the nominal mathematical time \(t_j=jh\). The FFT/RK4 routine receives the binary64 approximation to \(h\), which is included in the observed numerical output.

## Full Fourier-tensor difference, with exact rational summation

BSAR-16B defines a quadratic Gaussian-rational reference \(p(t)=a_0+t a_1+t^2a_2\). Each retained Fourier coordinate of \(H_j-p(t_j)\) is formed from the **exact integer ratios** of its binary64 real/imaginary components and the reference coefficients. Every coordinate discrepancy \(\delta_i\ge0\) is rounded upward to \(b_i=\lceil S\delta_i\rceil\) at \(S=10^{15}\), using integer arithmetic alone.

By Parseval,

\[
\|H_j-p(t_j)\|_2
\le\frac1S\sqrt{\sum_i b_i^2}.
\]

An integer square-root ceiling provides a second outward rational rounding, yielding the recorded bound \(D_j\). The verifier checks the **entire retained cube**, including tiny coefficients from numerical roundoff, and rejects nonfinite, nonzero-mean, or out-of-cube arrays. It performs no floating spectral norm reduction in the certificate.

The archived SHA-256 state-stream digests are computed from little-endian complex128 bytes in C order at **every time node**. The source, Python/NumPy versions, canonical JSON receipts, and each state hash are preserved. Independent CI replay recomputes the numerical arrays and all rational bounds. A different FFT implementation may generate different bits; the generated certificate is valid for the explicitly archived output.

## Exact continuous Galerkin error at each time node

For the exact continuous finite Galerkin ODE solution \(v_K(t)\), BSAR-16B supplies the rigorous rational majorant

\[
Y(t)=E\left(\sum_{i=0}^{2}\frac{G_it^{i+1}}{i+1}\right)
\sum_{i=2}^{4}\frac{\mathcal D_it^{i+1}}{i+1}
\ge\|v_K(t)-p(t)\|_2,
\]

with \(\mathcal D_i\ge\|d_i\|_2\), \(G_i\ge\sum_k|k||\hat a_{i,k}|\), and an exact rational upper exponential \(E(x)=(1-x/m)^{-m}\ge e^x\). Thus

\[
\boxed{\|H_j-v_K(t_j)\|_2\le D_j+Y(t_j).}
\]

The real, divergence-free interpreted snapshot is \(W_j=\mathbb P P_{\rm real}H_j\), with conjugate symmetrization \(P_{\rm real}\) and exact Leray projection \(\mathbb P\). Both are \(L^2\) contractions fixing the exact Galerkin field, so

\[
\|W_j-v_K(t_j)\|_2\le D_j+Y(t_j)
\]

holds as well. The certificate does not need to compute these exact projected coefficients in order to invoke their contraction properties.

## Galerkin core anchors for the interpreted numerical Fourier field

The exact BSAR-14 anchors have initial vorticity norm \(\sqrt{26}N\), global continuum vorticity envelope \(\sqrt{65}N\), and initial normalized direction difference squared \(50/13\).

For \(K=(M-1)//3\), the finite Fourier inverse-gradient constant satisfies

\[
C_K=\sqrt{\sum_{k\in\Lambda_K}|k|^2}
=\sqrt{K(K+1)(2K+1)^3}.
\]

Since the quadratic rational reference begins at the true initial datum, its pointwise curl drift is bounded by \(G_1t_j+G_2t_j^2\). Directly from the observed binary64 Fourier tensor,

\[
\|\operatorname{curl}W_j-\omega_0\|_\infty
\le G_1t_j+G_2t_j^2+C_KD_j=:\varepsilon_j^{\rm direct}.
\]

A separate, weaker transfer through the exact Galerkin ODE uses

\[
\varepsilon_j^{\rm via\,G}
=G_1t_j+G_2t_j^2+C_KY(t_j)+C_K(D_j+Y(t_j)).
\]

Both formulas are evaluated with upward rational bounds. Given an upper \(\varepsilon\), the source anchors belong to the **continuous spatial half-maximum vorticity core** of the corresponding mathematical real Fourier field whenever

\[
(2\sqrt{26}-\sqrt{65})N-3\varepsilon>0.
\]

A positive direction-cone witness follows from the certified direction separation

\[
\sqrt{50/13}-\frac{4\varepsilon}{\sqrt{26}N-\varepsilon}
\]

and the exact distance between anchors \(\pi/N\), using \(N/\pi>7N/22\). Every required square root and final margin is rounded in the mathematically safe direction, using BSAR-16C's existing rational helper.

The result covers discrete **time nodes** and the continuous **spatial** torus. It does not transfer pointwise vorticity to a full infinite-dimensional Navier–Stokes solution.

## Verified 256-node receipts

The [dedicated BSAR-16D run](https://github.com/patrickdugan/MathCan/actions/runs/45008069630) passed its five targeted tests, certified all 16 numerical trajectories and 256 registered time nodes, and completed the independent replay of the archived rational bounds and binary64 state-stream SHA-256.

The canonical JSON campaign archive SHA-256 is:

    9ef44ff668bb98e4c0d8ac925e13842ed10f3fa4230fd7ede2dd6740837c8e58

The measured **rigorous rational upper bounds** are grouped below by the least favorable phase and time-step at the indicated grid. Error values are rounded **upward**, and continuous-spatial half-core margins are rounded **downward** for display.

| Initial N | Grid M | Max over time nodes of \(\|H_j-v_K(t_j)\|_2\) | Min direct core margin | Min via-Galerkin core margin |
|---:|---:|---:|---:|---:|
| 1 | 16 | ≤ 0.00001051 | ≥ 1.3680 | ≥ 1.3613 |
| 1 | 24 | ≤ 0.00001051 | ≥ 1.3644 | ≥ 1.3498 |
| 1 | 32 | ≤ 0.00001051 | ≥ 1.3560 | ≥ 1.3221 |
| 2 | 16 | ≤ 0.0001261 | ≥ 0.9124 | ≥ 0.8261 |
| 2 | 24 | ≤ 0.0001314 | ≥ 0.8652 | ≥ 0.6697 |
| 2 | 32 | ≤ 0.0001324 | ≥ 0.6804 | ≥ 0.2230 |

All 256 nodes satisfy the source-pinned continuous spatial half-maximum core criterion **under both the direct snapshot audit and the more conservative transfer through the exact Galerkin path**. Both calculations retain a positive rational lower bound for the normalized-direction cone witness.

The largest observed exact a posteriori bound occurs at \(N=2\), \(\sigma=-1\), \(M=32\), \(h=1/1000\): the final upper bound is approximately \(0.00013237323477680526\). The raw binary64 output's rational distance from the independent Taylor reference is bounded by approximately \(0.0000568477541\), with the remaining allowance supplied by the exact Galerkin trajectory enclosure. This error is an upper bound on Fourier coefficient-space error at the time nodes, rather than a numerical inter-resolution difference. The two 32-grid time-step variants have close but distinct SHA-256 state streams and independently certified bounds.

The 256 nodes comprise exactly 4 phase/frequency sources times (3 coarse runs of 13 nodes plus one fine run of 25). Each archived run stores a digest of all its binary64 coefficient arrays, plus explicit rational values for every time-node error and core witness. To recover all raw coefficients, rerun the pinned BSAR-15 Fourier integrator; the replay step checks that their canonical state-stream digests and certificates match the archive. The 14-day CI artifact provides the manifest, source hashes and receipts.

## Registered campaign and reproduction

All sixteen original BSAR-15 source scenarios are included: \(N=1,2\), \(\sigma=\pm1\), grids \(M=16,24,32\) at \(h=1/1000\), with a second \(M=32\) run per source using \(h=1/2000\). The coarse runs have 13 nodes and the fine runs 25, for **256 rational-certified numerical snapshots**.

The dedicated CI pins NumPy 2.3.5, checks the original BSAR-14 source blob, runs malformed-input and exact-coordinate controls, generates rational receipts and binary state digests, then independently reruns the entire campaign to validate the archived evidence.

Reproduce from the MathCan repository root using Python 3.11 and NumPy 2.3.5:

    python -m unittest experiments.bsar16.test_float64_snapshots -v
    python -m experiments.bsar16.float64_snapshots generate --out /tmp/bsar16d
    python -m experiments.bsar16.float64_snapshots audit --out /tmp/bsar16d

**Remaining BSAR-16 gates:** rigorous local arithmetic defects for the full FFT/RK4 evolution between nodes, quantitative transfer-sign persistence intervals, and higher-derivative full-PDE error bounds sufficient to transfer vorticity-core geometry to the true NSE solution. The analytic BSAR-09 global window budget remains open.

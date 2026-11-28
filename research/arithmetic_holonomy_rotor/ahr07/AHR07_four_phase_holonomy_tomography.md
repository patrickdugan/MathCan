# AHR-07: Four-setting signed-holonomy tomography

**23 November 2026.** Research note with exact finite-graph reduction, conditional classical Fisher-information bound, and seeded numerical oracle. These are project specializations of gauge-on-graph and phase-cycling methods. Priority claims and physical interpretation remain open.

## Model and theorem

Let G be a finite connected unicyclic graph with unique simple even cycle C of length L=2m. All site potentials are real, all hopping magnitudes J_e are positive, and a gauge transformation concentrates the only physical cycle phase theta on a closing edge. From vertex x on C, measure the return probability

\[
P_x(t,\theta)=|\langle x|e^{-itH_\theta}|x\rangle|^2.
\]

For each subset S of cycle edges, define P_{x,S} using only edges in S, with all non-cycle tree edges retained, and let D_C denote the L-fold signed finite difference over S. Removing any cycle edge turns G into a tree, and every edge phase of a tree is removed by a diagonal unitary. Therefore P_{x,S}(t,theta) is independent of theta for every proper S. For any offsets delta_j and weights w_j satisfying sum_j w_j=0, the exact reduction theorem is

\[
\boxed{\sum_j w_jD_CP_x(t,\theta+\delta_j)
=\sum_jw_jP_x(t,\theta+\delta_j).}
\tag{AHR-07A}
\]

This equality holds at arbitrary t. It generalizes to a marked cycle in a larger graph whenever every proper mask leaves the probed phase on a bridge, meaning that phase participates in no surviving cycle.

## Fourier quadrature and short-time cycle response

The one-flux, real-hopping graph has a real cosine Fourier series

\[
P_x(t,\theta)=a_0(t)+\sum_{k\ge1}a_k(t)\cos(k\theta).
\]

Closed-walk expansion for a cycle of even length L gives

\[
a_1(t)=\beta_Lt^L+O(t^{L+2}),\qquad
\beta_L=4(-1)^{L/2}\prod_{e\in C}J_e/L!,
\quad a_k(t)=O(t^{kL})\ (k\ge1).
\tag{AHR-07B}
\]

Set delta=(0,pi/2,pi,3pi/2). Measure the same intact-graph return probability at these four calibrated offsets and compute

\[
Z_4=\frac12\sum_{j=0}^3P_x(t,\theta+\delta_j)e^{-i\delta_j}.
\]

Fourier orthogonality yields the exact identity

\[
\boxed{Z_4=a_1e^{i\theta}+a_3e^{-3i\theta}
+a_5e^{5i\theta}+a_7e^{-7i\theta}+\cdots.}
\tag{AHR-07C}
\]

The second harmonic vanishes exactly. The first alias is third winding, of order t^(3L). Calibrate the real signed a_1(t) from a matched exact simulation and estimate theta as arg(Z_4/a_1). The phase is signed **relative to the controlled phase-offset reference**. When the sum of higher aliased magnitudes r is less than |a_1|, the noiseless angular bias is bounded by arcsin(r/|a_1|).

The three-setting DFT at (0,2pi/3,4pi/3) is minimally identifiable for an unknown affine first-harmonic baseline and two quadratures; it aliases the second harmonic, of order t^(2L), into the phase estimate. Four settings make a better experimental starting point.

## Conditional classical shot lower bound

In the small-harmonic Bernoulli model p_j=a+b*cos(theta+delta_j) with total B independent return/no-return shots allocated equally across four phases, let v=a(1-a). At leading order in b the phase score is orthogonal to the nuisance baseline and amplitude scores. Classical Fisher information is

\[
{\cal I}_\theta=\frac{B b^2}{2v}(1+o(1)),\qquad
\operatorname{Var}(\hat\theta)\ge\frac{2v}{B b^2}(1+o(1)).
\tag{AHR-07D}
\]

For an initial vertex x, a=1-kappa*t^2+O(t^4), where kappa is the sum of squared edge magnitudes incident on x; b=beta_L*t^L+O(t^(L+2)). Thus the local asymptotic bound is

\[
\boxed{\operatorname{Var}(\hat\theta)\gtrsim
\frac{2\kappa}{B\beta_L^2}t^{-(2L-2)}.}
\tag{AHR-07E}
\]

For uniform J=1 and degree two this is 144/(B*t^6) for L=4, and 129600/(B*t^10) for L=6. Fourier quadratures attain the leading Fisher bound under the stated model. This is a *conditional local classical Cramer-Rao bound for this fixed return-probability readout family*, not a general quantum metrology or quantum complexity lower bound. Collective/coherent measurements, other initial states, and adaptive protocols lie outside its assumptions.

## Exact same-expectation shot comparison

Let K=2^L. Four intact-graph phase measurements require 4 circuit settings. A directly parity-summed four-phase D_C estimator uses 4K configurations. Their expectations are identical by AHR-07A. With fixed total shots B, equal allocation, and v_j=p_j(1-p_j), the intact-graph Fourier real variance is (v_0+v_pi)/B. For the masked parity estimator it is (K/B)*sum_S(v_{0,S}+v_{pi,S}); analogous formulas hold for the imaginary quadrature. When per-setting Bernoulli variances are comparable, the masked estimator has approximately K^2=4^L times more quadrature variance. These calculations compare the explicitly defined estimators and shot allocations, rather than universally optimal masked procedures.

Any phase-independent affine readout channel p_observed=u+eta*p_ideal with eta>0 changes Z_4 to eta Z_4 and preserves its angle. More general readout confusion and coherent gate errors require empirical calibration.

## Numerical check and controls

Run python ahr07_ci.py, requiring NumPy and SciPy. It rebuilds the Hermitian matrices from prime-logarithm diagonal energies and a 4- or 6-edge cube cycle, checks gauge invariance for every broken-cycle mask, evaluates full-mask versus intact-graph Fourier estimators, computes cosine harmonics, and simulates 2,500 independent binomial experiments with seed 20261123.

Both experiments use a known implanted theta=0.73 radians and equal total budget B=8192 shots. For the two-qubit square at t=1.6, a_1=-0.255094, a_2=0.039978, a_3=0.000428, four-setting phase RMSE=1.37 degrees, and exhaustive masked-four-phase RMSE=21.16 degrees (4 versus 64 circuits). For a three-qubit hexagon with two attached tree leaves at t=2.5, a_1=-0.107135, a_2=0.007553, a_3=-0.00001235; angular RMSEs are 3.67 versus 93.25 degrees (4 versus 256 circuits). Equal-expectation identities hold at floating-point precision.

The **planted confounder** adds edge (4,5) to the hexagon with leaves, opening a shorter four-cycle sharing the probe edge. The exact intact-versus-mask quadrature equality then fails by 0.051401 at t=1.3. This negative control shows why an unmodified three-prime cube requires a cutset or more elaborate inverse problem, rather than the single-cycle formula.

## IBM handoff and research gates

Compile the four phase offsets as matched measured ISA circuits, with explicit Qiskit endianness checks, using current IBM SamplerV2 interfaces. Compare exact unitary synthesis and error-controlled product formulas; retain a disconnected/broken-loop control, phase-order randomization, layout and error receipts, and a matched hardware-noise simulator. Two-qubit primary target: t=1.6, nominal 2048 shots per phase. Three-qubit hexagon: t=2.5, first as a simulation-only target. Check account entitlements and estimated runtime before submitting. No paid fallback and no QPU submission without explicit authorization.

The next formalization gates are the finite-sum mask cancellation, forest gauge lemma, and the closed-walk first-harmonic coefficient in Lean. The connection to Riemann ellipsoids, the RH spectral problem, machine consciousness, and computational complexity remains speculative.

Current IBM Sampler documentation:
https://qiskit.qotlabs.org/docs/guides/get-started-with-sampler
https://quantum.cloud.ibm.com/docs/en/api/qiskit-ibm-runtime/server-side-sampler-sampler-v2

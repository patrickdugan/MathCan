# AHR-04: Spectral rigidity, fifth moments, and curvature tomography

**Date:** 2026-11-23. **Status:** exact elementary finite-dimensional derivations with numerical checks. The broad magnetic-graph trace framework is established prior mathematics; these are AHR-specific constructions and test proposals.

## Set-up

Let Q_d denote the binary d-hypercube for d>=2. For each vertex x, choose a real energy V_x. For each edge e={x,y}, choose a positive hopping magnitude J_e and oriented phase A_xy=-A_yx. Set

\[
H_A=\sum_x V_x|x\rangle\langle x|+\sum_{\{x,y\}}J_{xy}(e^{iA_{xy}}|x\rangle\langle y|+e^{-iA_{xy}}|y\rangle\langle x|).
\]

Let H_0 retain the same V and J with all phases zero. For every square face f, let F_f be its oriented flux, W_f the product of its four edge magnitudes, and S_f the sum of its four vertex energies.

## Theorem AHR-04A: fourth and fifth magnetic moments

\[
\mathrm{Tr}(H_A^k)=\mathrm{Tr}(H_0^k)\quad (k=0,1,2,3),
\]

\[
\boxed{\mathrm{Tr}(H_A^4)-\mathrm{Tr}(H_0^4)=8\sum_f W_f(\cos F_f-1),}\tag{1}
\]

\[
\boxed{\mathrm{Tr}(H_A^5)-\mathrm{Tr}(H_0^5)=10\sum_f W_f S_f(\cos F_f-1).}\tag{2}
\]

**Proof.** Expand trace powers into weighted closed walks with diagonal stays. Any gauge-sensitive closed walk in the bipartite cube must use at least four hopping edges. At four hops, the only nonbacktracking cycles are square faces; each face contributes four starting vertices in both orientations, yielding 8 W_f cos F_f. At length five the only gauge-sensitive walks use four square hops and one diagonal stay. Their five cyclic placements, four choices of stay vertex, and two orientations yield 10 W_f S_f cos F_f. Every other contribution has cancelling edge phases. Subtracting the zero-flux traces proves the formulas.

## Theorem AHR-04B: gauge rigidity

With positive magnitudes on every edge, define the fourth-moment defect

\[
\delta_4=\mathrm{Tr}(H_0^4)-\mathrm{Tr}(H_A^4)=8\sum_fW_f(1-\cos F_f)\ge0.
\]

Equality holds if and only if all face fluxes vanish modulo 2π. Every cycle of the hypercube reduces to square boundaries through cancellation and swapping of coordinate flips. Vanishing square flux therefore makes phase transport independent of path, producing a diagonal unitary D with H_A=D H_0 D†.

For uniform edge magnitude J, choose canonical root-to-vertex paths by enabling prime bits in increasing order. The gauge-fixed phase of any edge is a sum of at most d−1 square fluxes, from commuting its direction past larger already enabled coordinates. The triangle inequality on unit complex phases and Cauchy-Schwarz give the coarse stability estimate

\[
\boxed{\inf_D\|D H_A D^\dagger-H_0\|_F^2
\le\frac{d2^{d-1}(d-1)}{2J^2}\delta_4.}\tag{3}
\]

It bounds the ordered eigenvalue squared displacement as well by Hoffman-Wielandt. Removing edges can leave longer flux-bearing cycles, so rigidity is stated for the complete cube with positive weights.

## Theorem AHR-04C: arithmetic curvature localization

Let delta_5=Tr(H_0^5)-Tr(H_A^5). For delta_4>0, define w_f=W_f(1−cos F_f), and \bar V_f=S_f/4. Equations (1) and (2) imply

\[
\boxed{\frac{\delta_5}{\delta_4}=5\frac{\sum_f w_f\bar V_f}{\sum_f w_f}.}\tag{4}
\]

This is a curvature-weighted mean face energy. Its value lies between five times the smallest and largest face averages; a shift in the calibrated energy origin by u adds 5u.

For prime detunings V_x=Σ_i x_i log p_i, a face with lower corner s in prime directions i,j has average energy V_s+(log p_i+log p_j)/2. In the two-prime square with a nonzero flux,

\[
\boxed{\delta_5/\delta_4=(5/2)\log(pq).}\tag{5}
\]

For (p,q)=(2,3), the value is 4.479398673070137. Matching generic detunings reproduce this ratio: the primes enter through the chosen energy encoding.

## Theorem AHR-04D: recovering signed face phases

Fix the four edges e1,e2,e3,e4 of a face and independently toggle their hopping magnitudes between 0 and their calibrated positive values. Take the mixed four-edge finite difference of M_4=Tr(H_A^4), holding all other couplings fixed:

\[
\boxed{S_0=(\Delta_{e_1}\Delta_{e_2}\Delta_{e_3}\Delta_{e_4})M_4=8W_f\cos F_f.}\tag{6}
\]

This follows because a degree-four closed walk surviving all four differences must traverse each marked edge once, hence trace the selected square. Apply an additional +π/2 phase to the first edge along the oriented boundary. Its mixed difference is S_90=−8W_f sin F_f, giving

\[
\boxed{F_f=\operatorname{atan2}(-S_{90},S_0)\pmod{2\pi}.}\tag{7}
\]

Each mixed difference uses 16 on/off settings; recovering a signed face phase in this straightforward scheme takes 32 spectral-moment settings. The phase shift may affect neighboring faces, but the four-edge difference isolates the target. Hardware-efficient estimation and noise bounds remain open.

Global phase reversal is invisible to unprobed static spectra: H_{−A} is the complex conjugate of H_A, so their eigenvalues and diagonal return amplitudes coincide. The +π/2 probe fixes an orientation convention.

## Verification and research gates

AHR04 verifier performs 16 seeded random weighted-hypercube trials across d=2,3,4,5, tests the prime-two/prime-three ratio, signed phase inversion, a pure-gauge equality control, the canonical-gauge stability bound, and time-reversal ambiguity. Observed maximum absolute errors: 4.55e−13 for the fourth moment and 1.59e−12 for the fifth; phase inversion error 7.11e−15 modulo 2π.

The next work: Lean formalization of the closed-walk classification and discrete Poincaré statement; sixth-moment contributions from six-step circuits; controlled comparisons of prime logs and matched detunings; a noise-aware spectral estimator before IBM Quantum hardware. The AHR-03 four-oscillator model remains a surrogate for Riemann ellipsoids.

## Prior work and boundaries

- Korotyaev and Saburova, *Trace formulas for magnetic Schrödinger operators on periodic graphs and their applications* (2023): https://www.sciencedirect.com/science/article/pii/S0024379523002914
- *Closed walks of low dimension and twisted moments on self-loop graphs* (2025): https://doi.org/10.1007/s40840-025-01971-w
- Fabila-Carrasco, Lledó and Post, *Matching number, Hamiltonian graphs and magnetic Laplacian matrices* (2022): https://www.sciencedirect.com/science/article/pii/S0024379522000490

These identities establish neither RH nor a complexity-class advantage or machine consciousness. No QPU has been used.

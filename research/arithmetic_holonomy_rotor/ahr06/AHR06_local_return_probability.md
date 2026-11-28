# AHR-06: Local return-probability spectroscopy for gauge-threaded cycles

**23 November 2026.** Standalone mathematical continuation of AHR-04/05, with a hardware-accessible alternative to full trace reconstruction.

## Set-up

Let H_A be any finite Hermitian hopping Hamiltonian on a finite simple graph, with arbitrary real on-site energies, positive edge magnitudes J_e, and magnetic U(1) phases. Fix a **simple even cycle** C of length L=2m, with ordered edges e_1,...,e_L, cycle phase Phi_C, and edge product W_C.

As in AHR-05, D_C denotes the L-fold mixed finite difference obtained by independently switching the marked edge magnitudes between 0 and J_e. Hold other edges and all diagonal terms fixed. Choose the initial vertex x on C and define

\[
P_x(t)=|\langle x|e^{-itH_A}|x\rangle|^2.
\]

## Theorem AHR-06A: leading local-cycle return response

For every even simple cycle C,

\[
\boxed{
D_C P_x(t)=\frac{4(-1)^mW_C\cos\Phi_C}{L!}\,t^L
+O(t^{L+2}),\qquad t\to0.
}\tag{1}
\]

**Proof.** Expand the diagonal return amplitude as a power series in t. A length-L walk beginning and ending at x and containing every marked edge must traverse the entire cycle once. There are exactly two orientations, so D_C(H^L)_{xx}=2W_C cosPhi_C. When the modulus square is expanded, both the amplitude and its complex conjugate contribute this term, giving coefficient 4(-1)^mW_C cosPhi_C/L!. Any product of two shorter closed walks at x with combined length L, when restricted to C, uses fewer than L distinct edges: a closed walk shorter than C backtracks along its selected edges, so distinct selected edges consume at least two hops each. The mixed difference therefore removes every cross term at order t^L. The diagonal return probability is an even function of t for Hermitian H, excluding the next odd power. QED.

For L=4 the leading coefficient is +W_CcosPhi_C/6. For L=6 it is −W_CcosPhi_C/180.

A controlled +π/2 offset to one cycle edge changes the leading cosine to minus sine; two phase settings allow reconstruction of signed holonomy using only **basis-state return probabilities** rather than the whole spectral trace. The method still requires 2^L amplitude-toggle configurations per phase setting. At small times the signal is suppressed by t^L/L!, so shot noise and higher-order corrections are decisive design constraints.

## Numerical tests

The seeded oracle (Python, NumPy, SciPy) constructs arbitrary real diagonal energies, random edge couplings, and random flux on a two-qubit square and a three-qubit hexagon. At t=0.4,0.3,0.2 it evaluates the full 2^L mixed finite difference of the exact return probability and compares with the displayed leading monomial.

For the square, the measured-to-predicted ratios were approximately 0.79645, 0.88057, 0.94528. For the hexagon they were 0.77862, 0.87071, 0.94097. Both approach 1 as t decreases, consistent with the O(t^(L+2)) correction. These are finite-dimensional simulations rather than QPU measurements.

## Experimental gates

1. Optimize t to balance higher-order bias against shot noise for the 3-qubit hexagon, estimating the precision lost to the 64-term signed difference and its π/2 companion.
2. Compare return-probability protocols against the AHR-01 two-qubit flux pilot and AHR-05 exact mixed trace protocol at matched backend noise and total shots.
3. Preserve a zero-flux gauge control, a broken-cycle tree, a phase-reversed control, and matched arbitrary detuning controls.
4. Derive a moment-based estimator requiring fewer intervention settings, or prove a lower bound under a stated oracle model.
5. Formalize the marked-cycle return theorem in Lean. The Riemann ellipsoid connection is still a separate physical derivation.

No IBM hardware, quantum speedup, RH consequence, or consciousness claim is attached to this theorem.

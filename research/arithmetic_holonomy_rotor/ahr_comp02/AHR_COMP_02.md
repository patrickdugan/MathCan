# AHR-COMP-02: Sparse curvature and the limits of Gaussian computation

**Status:** Offline mathematical study and finite-dimensional CPU tests. Follows merged AHR-COMP-01 (#269). No IBM time was used. The Gaussian witness is relative to the fixed logical/fermionic encoding; no complexity separation is claimed.

## 1. Sparse defects in the pi-flux background

Use the little-endian prime cube with forward hopping H[x+e_i,x]=J exp(i A_i(x)), real energies sum_i log(p_i)x_i, and the Clifford background A_i=pi sum_(k<i) x_k. Allow at most one added phase term theta_i x_j(i) per hopping direction i, j!=i. Prefer distinct unordered pair supports in the benchmark: reciprocal directed terms can cancel in the curvature, so defect strength is a representation-dependent upper bound.

Let gamma_(2i)=Z_<i X_i, gamma_(2i+1)=Z_<i Y_i, and N_j=(I-Z_j)/2. The changed hopping equals J times

(1-N_j) gamma_(2i) + N_j[cos(theta) gamma_(2i)+sin(theta) gamma_(2i+1)]
= [(1+cos(theta))/2] gamma_(2i) + [sin(theta)/2] gamma_(2i+1)
  + Z_j {[(1-cos(theta))/2] gamma_(2i) - [sin(theta)/2] gamma_(2i+1)}.

Under the parity extension of COMP-01, gamma_a -> i g_* g_a, Z_j -> -i g_(2j) g_(2j+1). Thus the first line's quadratic portion has norm |J cos(theta/2)|, and the quartic part has norm |J sin(theta/2)|. This follows from the two anticommuting Majoranas and the commuting Z_j. If the quartic coefficient is nonzero, the normalized Q is a Hermitian involution consisting (up to a real sign) of four orthogonal Majoranas, one rotated within the target pair. For d>=3 these terms can generate non-Gaussian states in the specified parity encoding. The phase strength need not be small. The verifier checks 12 seeded Hamiltonian decompositions and the explicit isometry E|x>=(-i)^(|x| mod 2)|x, parity(x)>.

## 2. Additive-error tractability bound

Let H=G+sum_k w_k Q_k with G quadratic in the extended representation and w_k=|J sin(theta_k/2)|. Include the arithmetic detuning in G. Q_k is an even Majorana product and is itself a Gaussian unitary up to phase: pair the four orthogonal Majoranas and each pair product is a quadratic rotation through pi (up to sign/phase).

For a product formula of R steps, each quartic factor exp(-i a Q)=cos(a) I-i sin(a) Q has a two-branch Gaussian expansion. Both the quadratic factors and the two branch operators preserve the Gaussian family. The l1 norm of all path weights is

L=product_f (|cos(a_f)|+|sin(a_f)|) <= exp(sum_f |a_f|)=exp(Lambda_NG),

where Lambda_NG=|t| sum_k w_k for the usual first-order or symmetric splitting with positive substep magnitudes (for higher-order negative steps use total absolute time instead). This bound does not worsen merely by refining R. The conservative product-formula error can be made <=epsilon/constant with polynomial R at polynomial times, operator norms and inverse accuracy; this is separate from sampling.

For the vacuum amplitude A, sample a Gaussian trajectory b with probability |c_b|/L, and return L*(c_b/|c_b|)*<vac|U_b|vac>. This is unbiased for the product-formula amplitude and its magnitude is bounded by L. Hoeffding on real and imaginary parts gives O(exp(2 Lambda_NG) epsilon^-2 log(1/delta)) samples for amplitude error epsilon, with polynomial cost per trajectory using a **phase-sensitive** fermionic Gaussian overlap algorithm. Covariances alone do not track branch phases. Estimating the return probability to comparable additive accuracy follows by projection of the estimated amplitude onto the unit disk and squaring. Numerical precision and Trotter errors must be budgeted. Related phase-sensitive Gaussian and extent algorithms: Dias & Koenig, Quantum 8,1350 (2024), https://doi.org/10.22331/q-2024-05-21-1350; https://arxiv.org/abs/2603.18869.

The useful consequence: at polynomial time/precision costs and Lambda_NG=O(log d), this estimator has polynomial total cost. Dense defect count alone is insufficient evidence of hardness; high accumulated interaction strength only removes this particular guarantee. This is an upper bound, not an exponential classical lower bound or optimal simulation algorithm. The verifier checks exact branch summation and 20,000 draws on a small dense 3-qubit fixture (2 defects, R=3, t=1.2). It is not a measured scalable Gaussian simulator.

## 3. A constant-resolution, mixed-state-safe non-Gaussian witness

On d=3, use p=(2,3,5), J=1, defect A_0=theta*x_1, other directions at the pi-flux background. Let psi_x be the logical amplitudes of exp(-itH)|000>. A pure even four-mode Gaussian state obeys the Pfaffian amplitude equation c_empty*c_0123-c_01*c_23+c_02*c_13-c_03*c_12=0. For a nonzero vacuum amplitude this follows immediately from the exponential of a quadratic creation operator (Thouless form); continuity extends it to all pure even Gaussian states. Substituting the parity isometry yields the necessary condition B=0, where

B=psi_0 psi_7 - psi_3 psi_4 + psi_5 psi_2 - psi_1 psi_6,
C=2|B|=|psi^T S psi|,
S pairs complementary bit strings with the indicated signs. S is real symmetric orthogonal. The same four-mode invariant underlies established convex-Gaussian criteria (Oszmaniec, Gutt & Kus, Phys. Rev. A 90,020302(R), https://doi.org/10.1103/PhysRevA.90.020302).

At short times, the single-hop amplitudes are -iJt; the affected pair amplitude is -J^2 t^2(e^{i theta}-1)/2, and the other pairs vanish at order t^2. The sum over six triple paths is e^{i theta}-1, giving psi_7=iJ^3 t^3(e^{i theta}-1)/6+O(t^4). Real diagonal detuning cannot enter the leading minimum-hop paths. Therefore

B= -i J^3 t^3 (e^{i theta}-1)/3+O(t^4),
C=(4/3)|Jt|^3 |sin(theta/2)|+O(t^4).

A nonzero defect creates a nonzero Gaussian obstruction in this fixed encoding. A vertex gauge transform can change the encoding-relative witness, so never report this as a gauge-invariant magic measure.

For a pure target psi, every normalized isotropic phi (phi^T S phi=0) has squared overlap bounded by

F_G(psi)=(1+sqrt(1-C^2))/2.

Proof: make a unitary change of coordinates M with M^T S M=I (diagonalize S, multiply its negative eigenvectors by i). Choose target global phase so z^T z=C is nonnegative. Then z=a u+i b v for real orthonormal u,v, a^2=(1+C)/2, b^2=(1-C)/2. An isotropic vector is (e+i f)/sqrt(2) with real orthonormal e,f, so its overlap magnitude with each real unit vector is at most 1/sqrt(2). Triangle inequality bounds the overlap by (a+b)/sqrt(2). Taking e=u,f=v attains the bound in the isotropic superset. Degenerate b=0 is handled by any perpendicular v. By linearity every mixture of pure even Gaussian states obeys <psi|rho|psi><=F_G. Thus a fidelity lower bound above F_G is a certificate against that convex set, even for noisy mixed logical states. No pure-state assumption about the observed rho is needed; a nonzero covariance deficit alone would not be such a certificate.

Freeze the target by scanning theta in {pi/4,pi/2,3pi/4,pi}, t=0.025..4.0, step 0.025. Best candidate: theta=pi, t=1.325, C=0.72900352, F_G=0.84225497. The detuned zero-defect evolution has C<1e-12 across the grid. This is an ideal design optimization, not selection using hardware counts. The target vector is recorded in validation.json. Under illustrative logical global depolarization rho=(1-p)|psi><psi|+p I/8, the noiseless-readout threshold is p<0.18028. A physical device need not obey this channel.

## 4. A measurable three-qubit pilot

Expand the fixed projector P=|psi><psi| as (1/8) sum_Pauli r_P P, r_P=<psi|P|psi>. Measure with the 27 local XYZ basis settings. Assign each nonidentity Pauli to the product setting obtained by replacing its I letters with Z. Identity contributes 1/8 exactly. Within each group g use the per-shot score sum assigned (r_P/8)*product of measured eigenvalues. Its range is at most 2 W_g, W_g=sum assigned |r_P|/8. With independent shots, a one-sided Hoeffding 95% lower confidence bound on fidelity subtracts sqrt(2 log(20) sum_g W_g^2/n) for n shots per group. Include a separate calibrated systematic allowance for SPAM, layout changes, measurement rotations and preparation drift; the ideal bound is not a guarantee on device bias.

The verifier checks the Pauli sum, grouped scores and 2,000 Monte Carlo trials at each illustrative noise level. With 2,048 shots/setting the 27 target circuits use 55,296 shots; statistical radius 0.02820. At 10% ideal global depolarization all 2,000 trials cleared the Gaussian ceiling; at 15%, 41.25% did. At 4,096 shots/setting the radius is 0.01994 and 90.45% of 15%-depolarized trials clear the ceiling. These simulations omit actual calibration and therefore cannot authorize hardware.

Hardware preparation: compare exact 3-qubit unitary versus structured sparse hopping product formulas, with fixed logical bit/phase convention and known prepared target. Use frozen ideal and compiled states, register fixed projector and statistical rule before acquisition, measure all groups and same-schedule zero-defect Gaussian control; require the control not to falsely certify. Add theta=pi/2 and repeated time/reversed-angle controls on independent settings if resources permit. Randomize execution order, use fresh calibration and account separately for readout/model uncertainty. Do not discard leakage or use posthoc target selection. A direct target-state fidelity test alone does not establish implementation of scalable Hamiltonian dynamics; compare compiled evolution and controls, not only a state-preparation shortcut. No hardware request or paid fallback; exact workload approval remains separate.

## 5. Next complexity gate

Register sparse defect schedules with independent held-out fields. Benchmark vacuum return and bounded local observables, with Gaussian path sampling, direct statevector, and tensor-network references at matched additive error, not runtime alone. Under switchable controls, non-Gaussian quartic rotations provide the known route beyond fermionic linear optics; this does not establish hard autonomous evolution. Investigate whether high-Lambda_NG bounded-degree systems yield useful inverse-polynomial signals before increasing d, and whether state preparation, native depth and measurement scale polynomially. Impagliazzo's worlds require independent results on complexity and average-case one-way/public-key primitives. No evidence from a three-qubit witness can decide between them.

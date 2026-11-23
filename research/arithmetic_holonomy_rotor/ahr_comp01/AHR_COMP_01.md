# AHR-COMP-01: compact arithmetic gauge fields and the complexity frontier

Status: mathematical derivations and CPU checks. No QPU usage. No complexity-class separation, RH consequence, or consciousness claim.

## 1. Exact compact gauge quotient

On the d-bit prime cube the forward hopping element is J exp(i A_i(x)) for x_i=0, with conjugate reverse. The diagonal is E(x)=sum_i log(p_i)x_i. Let each A_i be a Boolean multilinear polynomial of degree at most r in the other bits. Coefficients are angles modulo 2 pi. For i<j define the oriented face flux F_ij=Delta_i A_j-Delta_j A_i.

Group each directional coefficient a_(i,T) by S=T union {i}. A vertex potential monomial g_S x_S adds the same angle to all |S| coefficients. Uniqueness of Boolean multilinear coefficients follows from integral Mobius inversion, so gradients preserving degree <=r have potentials of degree <=r+1. Thus the quotient torus has dimension

g_r(d)=sum_(s=2)^min(d,r+1) (s-1) binomial(d,s).

For r=1 it is C(d,2); for r=2 it is C(d,2)+2 C(d,3). The unrestricted dimension is (d-2)2^(d-1)+1. Choose min(S) as an anchor and set its coefficient to zero. For each support S and each j in S excluding i=min(S), measure F_ij at the background indicator T=S excluding i,j. Exactly g_r(d) phase observations suffice: the coefficient b_(ij,T)=a_(j,T union {i})-a_(i,T union {j}) is

b_(ij,T)=sum_(U subset T) (-1)^(|T|-|U|) F_ij(1_U) mod 2 pi.

Every required smaller address is already selected. This triangular unimodular map reconstructs the anchored field. It is a minimal continuous scalar-coordinate count for local identification on an open chart. With circular errors <=epsilon per phase reading the coefficient error is <=min(pi,2^|T| epsilon); on an unwrapped chart, independent equal variance errors produce variance 2^|T| sigma^2 and shared-address covariance. Real hardware must still establish phase observability, systematic error, and shot cost.

## 2. An efficient fourth-moment classical reference

The weighted-square walk identity of AHR-03/04 yields

(Tr H_A^4 - Tr H_0^4)/2^d = 2 J^4 sum_(i<j) (E cos(F_ij)-1).

For quadratic edge fields each face flux is affine, b+sum_k c_k x_k. Independent uniform background bits give

E exp(i F_ij) = exp(i b) product_(k!=i,j) (1+exp(i c_k))/2.

Its real part evaluates the normalized fourth-moment deficit in O(d^3) arithmetic operations with indexed coefficients. The unchanged diagonal cancels. Compare with exact dense traces and exhaustive face sums in dimensions 3–6. This is a strong classical control, including the numerical precision needed by the observable.

## 3. Polynomial synthesis and control assumptions

With A_i diagonal on other bits, define D_i=exp(-i A_i Z_i/2). Then B_i=J D_i X_i D_i^dagger, since Rz conjugation gives cos(A_i) X_i+sin(A_i) Y_i. Each degree-k monomial is one k-controlled Rz in D_i, and exp(-i h B_i) conjugates one Rx by D_i. A Strang step has 2d-1 hopping factors, two diagonal layers and at most 4 sum_i nnz(A_i) phase rotations plus O(d) one-qubit rotations. Fixed r gives bounded arity. Native decomposition, routing and discrete gate synthesis remain costs.

Let Lambda=sum_i log(p_i)+d |J|. For R>=t Lambda, Taylor expansion through second order, the scalar exponential bound on the two tails, and unitary telescoping give the conservative error bound e Lambda^3 t^3/(3 R^2). For polynomial t, inverse error and prime-list bit lengths, fixed r admits polynomial synthesis. If M coefficients have error <=delta the Hamiltonian error is <= |J| M delta and evolution error <=t |J| M delta. This is an absolute-accuracy bound, not a guarantee of large measurable signals. Tighter product-formula bounds: Childs et al., DOI 10.1103/PhysRevX.11.011020.

Additional controls, such as isolating hopping directions, setting their phases, and switching off/refocusing the detuning, give the usual universal circuit primitives. Constant phases 0 and pi/2 give X and Y rotations; A_i=pi*x_j gives Z_j X_i. Commuting X_i and Z_j X_i implement exp(-i pi N_j X_i/2), a controlled -iX, and a control phase diag(1,i) completes CNOT. The verifier tests both the CNOT and phase conjugation. This is a statement about switchable generators, not universal autonomous static Hamiltonian computation.

## 4. Exact detuned pi-flux baseline

A_i=pi sum_(j<i) x_j gives Jordan-Wigner Majoranas gamma_(2i)=Z_<i X_i and gamma_(2i+1)=Z_<i Y_i. Then

H=cI+(i/2)sum_i log(p_i) gamma_(2i) gamma_(2i+1)+J sum_i gamma_(2i).

On d+1 fermionic modes, replace each gamma_a by i g_* g_a using the auxiliary Majorana g_*. These obey the Clifford relations and preserve even parity. Their pair products are g_a g_b. The original d-qubit representation is realized on the even parity subspace, with the all-zero vacuum as encoded initial state. The new Hamiltonian is quadratic, H'=cI+(i/4)g^T K g with real skew K. With the real vacuum covariance G0 (blocks [[0,-1],[1,0]] for G_jk=(i/2)<[g_j,g_k]>), evolution gives Gt=exp(tK)G0 exp(tK)^T. The pure Gaussian overlap is

P_pi(t)=2^-(d+1) sqrt(det(I-G0 Gt)).

Thus vacuum return uses a 2(d+1) square real matrix and O(d^3) dense arithmetic. With zero detuning this reduces to cos^2(J sqrt(d)t). Near-zero determinants require numerical care. This does not extend to all affine interacting fields. See fermionic Gaussian covariance/overlap methods, DOI 10.1103/PhysRevResearch.3.033188. Zero flux has the independent two-level product baseline.

## 5. Exact counting via degree-four phases and precision barrier

Encode the n inputs and m internal gates of a Boolean circuit C as m quadratic or linear gate constraints and one output constraint q_l=0 over GF(2). AND/XOR/NOT suffice. With a fresh multiplier bit y_l per constraint define f=sum_l y_l q_l mod 2. It has degree <=3. Summing (-1)^f over the multiplier bits annihilates every inconsistent assignment and gives 2^(m+1) on each valid satisfying assignment. Each input has a unique wire assignment. Therefore

E_(x,z,y)(-1)^f = #SAT(C)/2^(n+m).

Choose two marked prime directions i,j, remaining bits as the n+2m+1 background. A_j=pi*x_i*f and other phases zero give F_ij=pi*f, with real integer monomial coefficients implementing parity through exp(i pi f). Degree <=4. With only the i,j hopping directions active the graph is disjoint squares and the normalized fourth-moment difference is 2 J^4 (E cos F_ij - 1). Exact evaluation at J=1 recovers #CircuitSAT and hence is #P-hard under polynomial-time exact reductions. The code checks 26 Boolean circuits, including zero, one and all satisfying inputs. Related degree-three IQP gap amplitudes: Bremner, Montanaro and Shepherd, DOI 10.1103/PhysRevLett.117.080501.

However, direct recovery needs additive error <2^-(n+m+1); a one-solution instance has normalized signal 2^-(n+m). Uniform background samples give a cheap classical additive-error estimator with O(epsilon^-2 log(1/delta)) samples. Standard coherent amplitude estimation improves precision dependence to O(1/epsilon) uses under its coherent-access assumptions. Both generic query costs grow exponentially for this exact reduction. These are algorithmic upper bounds and a direct encoding resolution requirement, not a lower bound against every possible algorithm. No constant-error, average-case, or quantum computational advantage follows.

## 6. Frozen CPU protocol

Seed 20261124, J=1, t=0.7. Compare zero flux, the exact detuned pi-flux Gaussian oracle, compact affine/quadratic and pi-flux symmetric-product simulations at d=3,5,8,12,16,20. At d<=12 include an explicit unstructured control that randomly permutes each direction's phase table while preserving its phase marginal. Degree-two coefficients are scaled by sqrt(d-2). Test exact dense references at small d and compare steps 4,8,16 for the quadratic d=20 case. All are offline, single-seed implementation comparisons. No statistical speedup claim; durations exclude native compilation.

At d=20 the quadratic family has 2,470 independent angles and 1,048,576 vertices. The verifier uses 16 MiB state and 160 MiB explicit phase tables. Eight Strang steps use 76,000 logical controlled phase rotations before native synthesis, showing the dense compact family is not automatically practical for noisy hardware.

## 7. Research gates

Next: sparse bounded-degree curvature supports; independently specified supervised/prediction task and inverse-polynomial signal; fair classical baselines including Gaussian/product/phase-sum/Monte Carlo and tensor-network convergence. Compare recurrent models only with defined training/test data and full training/access cost. The five-world question depends on quantum average-case cryptographic hardness and BQP vs NP, which these results leave open. The classical and quantum resource model must include input preparation, simulation precision, measurements and compilation. AHR remains simulator-first. No new hardware run authorized.

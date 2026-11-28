# BSAR-16I: an exact L2 core obstruction and a quantitative H4 transfer criterion

Parent: [BSAR-16 #213](https://github.com/patrickdugan/MathCan/issues/213), issue [BSAR-16I #231](https://github.com/patrickdugan/MathCan/issues/231). The source is the exact BSAR-14 eight-mode divergence-free initial datum, pinned to MathCan commit e2c0e1c56f6e5d2291536156709f75668d1e0f8f and blob aa25ad74be2347acf061d631f55338802eead212. The finite-Galerkin vorticity-core inputs are independently recomputed from merged [BSAR-16C #217](https://github.com/patrickdugan/MathCan/pull/217), with row SHA-256 aabf443503a9f30b16f3a1e8701b1a187075091cdbc4c8e811e250ab06f925cb.

**What this stage proves:** a sequence of smooth divergence-free high-frequency perturbations with arbitrarily small L2 velocity error removes both original anchors from the full half-maximum vorticity core; and, independently, a concrete uniform sufficient \(H^4\) velocity-error threshold for transferring the certified **exact Galerkin** anchors and positive cone witnesses to a smooth full-PDE velocity field.

**What remains open:** Any actual bound on the full NSE–Galerkin \(H^4\) velocity difference through \(T=3/250=0.012\). Thus the sufficient threshold below is explicitly **conditional**. The BSAR-16B/H \(L^2\) estimates and almost-everywhere low-shell sign theorem alone do not imply it.

## 1. Exact small-L2 obstruction

Take the BSAR-14 real, divergence-free datum \(u_0\) at initial frequency \(N=1\) or \(2\), phase \(\sigma=\pm1\), amplitude \(1\). Its exact source vorticity anchors are

\[
x_0=(0,0,\pi/(2N)),\quad
x_1=(\pi/N,0,\pi/(2N)),\qquad
\omega_0(x_0)=(0,-N,-5\sigma N),\quad
\omega_0(x_1)=(0,-N,5\sigma N).
\]

Both magnitudes equal \(\sqrt{26}\,N<6N\), and the original entire field satisfies \(\|\omega_0\|_\infty\le\sqrt{65}\,N<9N\).

For any integer \(m\ge1\), define

\[
\delta_m=1/m,\qquad M_m=24Nm,\qquad
w_m(x,y,z)=(0,\delta_m\cos(M_m x),0).
\]

The field \(w_m\) is real, smooth, periodic, zero-mean and divergence-free, since its only nonzero component depends on \(x\). Its normalized L2 velocity norm is exactly

\[
\|w_m\|_2^2=\frac{\delta_m^2}{2}=\frac1{2m^2}\longrightarrow0.
\]

Its two Fourier coefficients are at \(\pm(M_m,0,0)\), each \((0,\delta_m/2,0)\). The vorticity perturbation is

\[
\nabla\times w_m=(0,0,-\delta_mM_m\sin(M_mx)).
\]

At both original anchors, the sine factor is zero because \(M_m/N=24m\) is an even integer. Their vorticities in \(u_0+w_m\) therefore remain exactly the source values. At \(x_*=\pi/(2M_m)\), the added curl has magnitude \(\delta_m M_m=24N\). The triangle inequality and original continuum upper bound imply

\[
\|\nabla\times(u_0+w_m)\|_\infty
\ge |\nabla\times(u_0+w_m)(x_*)|
\ge24N-\sqrt{65}\,N>15N.
\]

Consequently the half-maximum threshold exceeds \(15N/2>6N\), while both anchor norms remain below \(6N\). Both anchors lie strictly outside the actual continuum half-maximum vorticity core of \(u_0+w_m\), for every \(m\), even though its velocity L2 error tends to zero.

The script checks all Gaussian-rational Fourier coefficients, solenoidality, source anchor vorticities and integer phase identities. **This is an obstruction to a generic L2-to-core inference, not a claim that \(u_0+w_m\) is an NSE trajectory from the original initial condition.**

## 2. Exact lattice estimate for a pointwise curl bound from H4

Define the normalized inhomogeneous Sobolev velocity norm

\[
\|e\|_{H^4}^2=\sum_{k\in\mathbb Z^3}
(1+|k|^2)^4|\widehat e(k)|^2.
\]

For a periodic \(H^4\) field, absolute Fourier convergence and Cauchy–Schwarz give

\[
\|\nabla\times e\|_\infty
\le\sum_{k\ne0}|k|\,|\widehat e(k)|
\le C_4\|e\|_{H^4},\qquad
C_4^2=\sum_{k\ne0}\frac{|k|^2}{(1+|k|^2)^4}.
\]

Partition nonzero lattice vectors by \(\rho=\max_i|k_i|\). The \(\rho\)-shell contains exactly \(24\rho^2+2\) integer wavevectors, and each has \(|k|^2\le3\rho^2\) and \((1+|k|^2)^4\ge(1+\rho^2)^4\). For every integer \(R\ge1\),

\[
C_4^2
\le
\sum_{\rho=1}^R
\frac{3\rho^2(24\rho^2+2)}{(1+\rho^2)^4}
+\sum_{\rho=R+1}^{\infty}\left(\frac{72}{\rho^4}+\frac6{\rho^6}\right).
\]

By the elementary integral test, the tail is bounded above by

\[
\frac{24}{R^3}+\frac{6}{5R^5}.
\]

At \(R=8\), the exact rational finite sum plus tail is **strictly less than \(9\)**, as checked using Python Fraction, so

\[
\boxed{\|\nabla\times e\|_\infty<3\|e\|_{H^4}.}
\]

This is a global continuous-spatial torus inequality. No floating-point grid maximum or approximate zeta-function evaluation is involved.

## 3. Reuse the twelve source-pinned exact Galerkin anchors

BSAR-16C previously certified the two anchors for the **exact continuous Galerkin ODE** \(v_K(t)\), for \(N=1,2\), \(\sigma=\pm1\), and grids \(16^3,24^3,32^3\) through \(T=3/250\). The original BSAR-16C generator is independently re-run and its canonical SHA-256 checked before this stage accepts any source entries.

The directed-rational receipts pass the following conservative, source-wide inequalities for every \(t\in[0,T]\):

\[
\begin{aligned}
\|\omega_{v_K}(x_i,t)\|&>4
&&\text{for both anchors},\\
2\min_i|\omega_{v_K}(x_i,t)|-\|\omega_{v_K}(t)\|_\infty
&>\frac35,\\
|\xi_{v_K}(x_0,t)-\xi_{v_K}(x_1,t)|&>1.
\end{aligned}
\]

The proof checks the original source-to-Galerkin curl drift upper bounds, which are below \(27/100\) for \(N=1\) and below \(61/50\) for \(N=2\), and checks all three displayed inequalities against each of the twelve actual rational records. These inequalities refer to the **original two anchor points**. They do not characterize the geometry of the entire high-vorticity core.

## 4. Conditional transfer to a full-PDE velocity field

Suppose a smooth periodic divergence-free full-PDE velocity \(u(t)\) exists on the registered interval with the same initial datum and obeys the additional quantitative estimate

\[
\boxed{\sup_{0\le t\le T}\|u(t)-v_K(t)\|_{H^4}\le\frac1{20}.}
\tag{H4}
\]

This **H4 bound is an unproved hypothesis** of the present stage. With \(e=u-v_K\), the previous lattice inequality gives pointwise everywhere in space and for all registered times,

\[
\|\omega_u(t)-\omega_{v_K}(t)\|_\infty
<\frac3{20}=:\varepsilon.
\]

At both anchors the true vorticity magnitude is at least the Galerkin anchor magnitude minus \(\varepsilon\), while its continuous global maximum is at most the Galerkin global maximum plus \(\varepsilon\). The strict half-core margin is therefore

\[
2\min_i|\omega_u(x_i,t)|-\|\omega_u(t)\|_\infty
>\frac35-3\frac3{20}=\frac3{20}>0.
\]

The anchor vorticity norms stay above \(4-\varepsilon>0\). The normalized direction perturbation bound gives

\[
|\xi_u(x_0,t)-\xi_u(x_1,t)|
>1-\frac{4\varepsilon}{4-\varepsilon}
=1-\frac{12}{77}=\frac{65}{77}>\frac45.
\]

The shortest torus distance between the two anchors is \(\pi/N\), and \(\pi<22/7\). Thus the true full-PDE core's anchored vorticity-direction quotient satisfies

\[
\boxed{
K_{\xi,u}(t)>
\frac{7N}{22}\left(\frac45\right)^2
=\frac{56N}{275}>0,\qquad 0\le t\le T,
}
\]

**conditional on (H4) and smooth existence on that interval**. The code computes case-specific, sharper rational margins from the original BSAR-16C receipts and also verifies these conservative uniform bounds.

One may apply the same implication at almost every time for a suitable weak velocity whenever an \(H^4\) difference bound holds at those times, with its corresponding pointwise continuous spatial representative. The BSAR-16H Leray–Hopf comparison supplies only a velocity \(L^2\) error, so it does not currently satisfy this stronger hypothesis.

## 5. Reproduction and remaining analytic dependency

The standard-library Python verifier generates 24 exact high-frequency obstruction records for the four BSAR-14 source roots at six frequencies, the exact radius-8 infinite-lattice curl-embedding upper bound, and twelve conditional full-core transfer records from the independently re-audited BSAR-16C evidence. It saves canonical JSON and a SHA-256 manifest.

Reproduce from the MathCan root:

    python -m unittest experiments.bsar16.test_core_transfer_frontier -v
    python -m experiments.bsar16.core_transfer_frontier generate --out /tmp/bsar16i
    python -m experiments.bsar16.core_transfer_frontier audit --out /tmp/bsar16i

**Next actual proof obligation:** derive and evaluate an a posteriori **\(H^4\) full-PDE-vs-Galerkin error enclosure** and a quantitative local strong-existence interval for these four exact sources. Work on rigorous approximate-solution stability in higher Sobolev norms by Morosi and Pizzocchero (Nonlinear Analysis 75, 2012, DOI 10.1016/j.na.2011.10.020), and the a posteriori 3D NSE regularity criterion by Chernyshenko, Constantin, Robinson and Titi (J. Math. Phys. 48, 2007, DOI 10.1063/1.2372512), gives relevant frameworks. The present conditional \(1/20\) criterion can serve as a registered quantitative acceptance target for that work.

The full-PDE pointwise core, classical global regularity, uniqueness, and the BSAR-09 uniform-in-frequency dimensionless window budget remain open.

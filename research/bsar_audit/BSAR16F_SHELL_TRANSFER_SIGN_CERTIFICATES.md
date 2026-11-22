# BSAR-16F: exact-rational shell-transfer signs for the continuous Galerkin ODE

Parent [BSAR-16 #213](https://github.com/patrickdugan/MathCan/issues/213); target [BSAR-16F #222](https://github.com/patrickdugan/MathCan/issues/222). The input is the exact BSAR-14 initial eight-mode field, Fourier-normalized on the \(2\pi\)-periodic three-torus, and the independent BSAR-16B rational second-degree Taylor reference. The underlying source Git blob is pinned to \`aa25ad74be2347acf061d631f55338802eead212\`.

**Evidence scope:** strict sign-persistence intervals for the three nonlinear shell transfers of the **exact continuous finite-dimensional Navier–Stokes Fourier–Galerkin ODE**, with \(N\in\{1,2\}\), phase \(\sigma\in\{-1,+1\}\), viscosity \(\nu=1/10\), amplitude \(A=1\), retained cube \(K\in\{5,7,10\}\), and registered horizon \(T=3/250=0.012\). The certificate uses exact Gaussian-rational polynomial operations, directed-rational square-root bounds, and a written analytic trilinear inequality. The full infinite-dimensional NSE transfer signs require additional PDE error control.

## The transfer functional and exact source constraints

For a real, mean-zero solenoidal Fourier field \(w\), define

\[
T_s(w)=-\operatorname{Re}
\sum_{|k|^2=sN^2}
\overline{\widehat w_k}\cdot
\mathbb P_k\widehat{(w\cdot\nabla)w}_k,
\qquad s\in\{1,4,5\}.
\]

All sums use the spatial-average \(L^2\) normalization, and the Leray multiplier is the exact rational matrix \(I-kk^\top/|k|^2\). The BSAR-14 initial datum has

\[
T_1(0)=\sigma N/4,\quad
T_4(0)=-\sigma N,\quad
T_5(0)=3\sigma N/4,
\quad \sum_s T_s(0)=0.
\]

The source's three spectral shells are represented by 6, 6 and 24 integer wavevectors, respectively, at each supported cutoff. The nonzero source coefficients are independently checked against the original Gaussian-rational BSAR-14 convolution/projection oracle. At \(t=0\), their source shell gradient-weighted Fourier sums are \(2N,2N,5N\), which add to the exact \(9N\) source gradient sum used by BSAR-16C.

## Exact polynomial of degree at most six

From the BSAR-16B reference

\[
p(t)=a_0+ta_1+t^2a_2,
\qquad a_0=u_0,\quad a_1=F_K(a_0),\quad
a_2=\tfrac12 DF_K(a_0)[a_1],
\]

the exact unaliased rational convolution gives

\[
\mathbb P B(p(t),p(t))
=\sum_{j=0}^4 t^j b_j,\quad
b_j=\sum_{i+\ell=j}\mathbb P B(a_i,a_\ell).
\]

Therefore the shell transfer is a degree-at-most-six polynomial,

\[
T_s(p(t))=\sum_{r=0}^6 c_{s,r}t^r,
\quad
c_{s,r}=-\operatorname{Re}\sum_{\substack{i+j=r\\|k|^2=sN^2}}
\overline{(a_i)_k}\cdot (b_j)_k .
\]

The code writes all seven coefficients as exact reduced rational numerator/denominator strings. An independent exact evaluation recomputes \(\mathbb P B(p(t),p(t))\) directly at rational times, verifying the polynomial expansion and the original time-zero signed source transfers.

For a sign \(h_s=\operatorname{sign}(c_{s,0})\) and \(0\le t\le\tau\), positivity of powers gives the exact rational lower bound

\[
h_s T_s(p(t))\ge
M_s^{\mathrm{ref}}(\tau):=
|c_{s,0}|+\sum_{r=1}^6
\min(0,h_s c_{s,r})\tau^r.
\]

This signed interval method retains helpful coefficients and only charges variation that can reduce the initial sign. It applies to **every real time in the interval**, rather than sampled times.

## Shell-local transfer perturbation bound

Let \(v_K\) be the exact continuous Galerkin ODE solution with the same initial field. BSAR-16B supplies the rigorous a priori \(L^2\) comparison

\[
e=v_K-p,\qquad \|e(t)\|_2\le Y(\tau),\quad0\le t\le\tau,
\]

where \(Y(\tau)\) is the upward-rational Gronwall envelope formed from the rational Taylor ODE defect. For this stage the rational exponential majorant uses a **fixed** subdivision integer, chosen at the registered \(T\), so all coefficient bounds are monotone for \(0\le\tau\le T\).

Define the trilinear Fourier-shell functional

\[
\tau_s(a,b,c)=\langle Q_sa,(b\cdot\nabla)c\rangle,
\]

where \(Q_s\) projects onto \(|k|^2=sN^2\). All fields are real and divergence-free. Integration by parts on the periodic torus gives

\[
\tau_s(a,b,c)=-\langle c,(b\cdot\nabla)Q_sa\rangle,
\qquad
|\tau_s(a,b,c)|\le
\|\nabla Q_sa\|_\infty\|b\|_2\|c\|_2.
\]

For the exact lattice shell \(\mathcal S_s=\{k\in[-K,K]^3:|k|^2=sN^2\}\), the Fourier Cauchy–Schwarz inequality gives

\[
\|\nabla Q_se\|_\infty
\le C_s\|e\|_2,\qquad
C_s=\sqrt{sN^2\,|\mathcal S_s|}.
\]

The exact rational reference admits

\[
\|p(t)\|_2\le P(\tau)
:=\sum_{i=0}^2\tau^i\|a_i\|_2,
\]

\[
\|\nabla Q_sp(t)\|_\infty\le G_s(\tau)
:=\sum_{i=0}^2\tau^i
\sum_{k\in\mathcal S_s}|k|\,|(a_i)_k|.
\]

The code bounds each square root **upward** by a rational at a \(10^{-9}\) scale. Expanding the exact cubic functional in \(p+e\), including all one-error, two-error and three-error terms, yields

\[
\boxed{
|T_s(v_K(t))-T_s(p(t))|\le
Y(C_sP^2+2G_sP)+
Y^2(2C_sP+G_s)+C_sY^3
=:\mathcal E_s(\tau)
}
\]

for every \(0\le t\le\tau\), where \(P=P(\tau)\), \(G_s=G_s(\tau)\), \(Y=Y(\tau)\). This inequality uses the finite shell size and source-aware reference shell coefficient support; it avoids a full-cube high-frequency derivative constant in the transfer perturbation.

The **strict sign gate** is

\[
\boxed{
M_s(\tau)=M_s^{\mathrm{ref}}(\tau)-
\mathcal E_s(\tau)>0.
}
\]

When it holds, the exact Galerkin transfer \(T_s(v_K(t))\) has the original BSAR-14 sign throughout \([0,\tau]\). Every gate is evaluated in exact rational arithmetic. Positive lower bounds are rounded **downward**, and perturbation upper bounds **upward**, for the archived display receipts. If the full \(T=3/250\) sign gate fails, the checker searches rational dyadic subintervals and records the first strictly certified positive duration. A failure to certify the full horizon is preserved as such rather than silently equated with the numerical trajectory.

## Sealed 36/36 sign-persistence receipts

The [first dedicated BSAR-16F run](https://github.com/patrickdugan/MathCan/actions/runs/45014808927) passed all six targeted tests, generated 12 source/grid cases and 36 shell records, and completed independent exact-rational archive replay. All 36 shell certificates prove their original signed transfer remains strictly positive **for every real time in the full registered window** \(0\le t\le3/250\). The source exact parity, BSAR-16B regression, BSAR-02 corpus, and broad mathematical/Lean workflows also passed on the same PR head.

The canonical SHA-256 of the exact-rational JSON records is

    daf4ebdd3b3d514beaae20381f6af9fb4c2f448b6edc04c6b8d8f5212e9ed6f3

The table reports, for each initial frequency and shell, the **least** certified signed transfer lower bound among both phase signs and all three grid sizes, evaluated over the entire continuous interval. Values are rounded *downward* for display; the full exact-rational records preserve the coefficients and directed errors.

| Initial frequency N | Shell \(\lvert k\rvert^2/N^2\) | Reference signed polynomial lower bound | Shell-local Galerkin transfer error upper | Certified exact-Galerkin signed transfer lower bound |
|---:|---:|---:|---:|---:|
| 1 | 1 | 0.243697700622 | 0.000102033660 | **0.243595666962** |
| 1 | 4 | 0.975923482352 | 0.000139372592 | **0.975784109761** |
| 1 | 5 | 0.695676988235 | 0.000320167115 | **0.695356821120** |
| 2 | 1 | 0.462721875724 | 0.002849368674 | **0.459872507050** |
| 2 | 4 | 1.856564679217 | 0.003511238865 | **1.853053440352** |
| 2 | 5 | 1.247010844613 | 0.008020160337 | **1.238990684277** |

The global minimum signed transfer lower bound is **0.243595666962** (N=1, phase -1, grid 32, shell 1). All cases keep the exact BSAR-14 initial signs \((\sigma,-\sigma,\sigma)\) for shells \((1,4,5)\). The worst registered Galerkin-minus-Taylor \(L^2\) upper bound underlying the perturbation estimate is \(7.5525481\times10^{-5}\), for N=2.

The intervals and full finite Fourier coefficients are certified using exact rational arithmetic. The proof establishes shell-transfer sign persistence for the **exact continuous Galerkin vector field**; the BSAR-15 float64 result was an empirical check of the same signs, with independent audit of its coefficient arrays in BSAR-16D/E.

## Tests, provenance and interpretation

The dedicated CI uses standard-library Python 3.11 only, with exact-source blob pinning. Independent tests verify the full BSAR-14 convolution/Leray shell coefficients, degree-six polynomial equality at several positive rational times, the rational interval minimum, explicit quadratic and cubic transfer-error terms, rejected malformed source arguments, and frozen SHA-256 corpus integrity.

The twelve registered phase/frequency/grid cases each produce three shell sign certificates, giving **36 exact-rational signed transfer records**. The source normalization and the proof boundary are explicit in the manifest, and the parent BSAR-16 issue remains open after this subgate.

Reproduction:

    python -m unittest experiments.bsar16.test_shell_signs -v
    python -m experiments.bsar16.shell_signs generate --out /tmp/bsar16f
    python -m experiments.bsar16.shell_signs audit --out /tmp/bsar16f

The BSAR-15 float64 RK4 results are used only for **post-certification comparison** of their observed signs. The rational proof applies to the exact finite Galerkin ODE, while transferring transfer-functional signs to the full infinite-dimensional NSE solution would need a suitable stronger velocity/derivative error estimate. It provides no frequency-uniform lifespan, global regularity theorem, or BSAR-09 window-budget estimate.

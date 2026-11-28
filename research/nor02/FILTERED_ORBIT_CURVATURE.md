# NOR-02: curvature-suppressed filtered recurrent orbits

**Provenance and status (15 November 2026).** New derivation in this research program from OpenAI Math **#094** (*Subpolynomial dimension reduction in Lp*, 23 September 2026) and **#325** (*A direct proof of the complete Crouzeix inequality*, 26 September 2026), pinned to source commit `openai/math@4eaee87548250b2682affda7d05d947c05554bae`. Mathematical priority relative to other literature has not been established. The analytic proof below is paper-level. `MathCan/FilteredOrbit.lean` proves the *separate discrete metric stitching* and noncommuting-coefficient identities; it does not kernel-check the complex functional calculus or the Gaussian/Lp embedding theorem.

- [Paper #094, LaTeX](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Subpolynomial-dimension-reduction-in-Lp-September-23-2026/build/paper.tex)
- [Paper #325, LaTeX](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex)
- [NOR-01 predecessor](../nor01/NUMERICAL_ORBIT_STITCHING.md)

## 1. Exact disk extremal for an exposed boundary zero

Let \(a,b>0\), \(q=a+b<1\), \(K=\{z\in\mathbb C:|z-a|\le b\}\), and \(t,r\) be positive integers. Define
\[
\mathcal M_{t,r}(K)=\max_{z\in K}|z|^t|z-q|^r,\qquad
\beta_{t,r}=\left(\frac{t^t r^r}{(t+r)^{t+r}}\right)^{1/2},
\qquad
\Gamma_{t,r}=(b/a)^{r/2}q^{t+r}\beta_{t,r}.
\]

**Theorem A (curvature extremal).**
\[
\mathcal M_{t,r}(K)\le\Gamma_{t,r}.
\]
If \(q^2t/(t+r)\ge(a-b)^2\), equality holds. Thus for each fixed \(r\), when the radial attainment condition holds,
\[
\mathcal M_{t,r}(K)=
(b/a)^{r/2}q^{t+r}
\left(\frac{t^t r^r}{(t+r)^{t+r}}\right)^{1/2}
=\Theta_{a,b,r}(q^t t^{-r/2}).
\]
The last asymptotic uses \(t^t/(t+r)^t\to e^{-r}\).

**Proof.** Write \(z=a+w\), \(|w|\le b\). Then
\[
|z-q|^2=|w-b|^2=b^2+|w|^2-2b\Re w
\le 2b(b-\Re w).
\]
Meanwhile
\[
q^2-|z|^2=b^2-|w|^2+2a(b-\Re w)
\ge2a(b-\Re w).
\]
Combining,
\[
|z-q|^2\le\frac ba(q^2-|z|^2). \tag{1}
\]
Put \(s=|z|^2/q^2\in[0,1]\), raise (1) to the \(r\)-th power and multiply by \(|z|^{2t}\):
\[
|z|^{2t}|z-q|^{2r}\le
(b/a)^r q^{2(t+r)}s^t(1-s)^r.
\]
The unique maximizer is \(s_*=t/(t+r)\); differentiation yields the stated beta expression. On \(|w|=b\), both inequalities in (1) are equalities. The possible squared moduli on this boundary circle are precisely \([(a-b)^2,q^2]\). If \(q^2s_*\) belongs to that interval, select a point with \(|z|^2=q^2s_*\) and obtain equality. \(\square\)

**Important boundary:** if \(a=0\), every boundary point maximizes \(|z|\); a zero at one point gives no uniform power-law improvement. The prefactor \((b/a)^{r/2}\) correctly diverges. The disk-shape assumption and the fact that \(q\) is the *actual* extreme radial point are essential for this argument.

For \(t=0\), the exact supremum is \((2b)^r\); the displayed \(\Gamma\) expression is still an upper bound with the convention \(0^0=1\). In this note the strict formula and the extremal attainment claim use \(t,r\ge1\).

## 2. Complete Crouzeix for a genuinely noncommuting filter

Define matrix-coefficient polynomials
\[
C(z)=\begin{pmatrix}0&1\\z&0\end{pmatrix}
=B_0+zB_1,\quad
B_0=\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
B_1=\begin{pmatrix}0&0\\1&0\end{pmatrix},
\quad
P_r(z)=(z-q)^r C(z).
\]
Here \(B_0B_1=\mathrm{diag}(1,0)\) and \(B_1B_0=\mathrm{diag}(0,1)\), so scalar-coefficient arguments do not cover the relevant matrix algebra. Moreover \(C(z)^*C(z)=\mathrm{diag}(|z|^2,1)\), and therefore \(\|C(z)\|=1\) for \(|z|\le q<1\).

Let \(A\in M_n(\mathbb C)\) with \(W(A)\subseteq K\). In the tensor-polynomial convention from paper #325,
\[
F[A]=\sum_{k=0}^{d}A^k\otimes F_k
\quad\text{for }F(z)=\sum_kz^kF_k.
\]
For an arbitrary \(u\in\mathbb C^n\otimes\mathbb C^2\), put
\[
v_t=[z^tP_r(z)][A]u.
\]
The **complete** Crouzeix bound from #325, applied *once* to the whole polynomial \(z^tP_r(z)\), gives
\[
\boxed{\ \|v_t\|_2\le2\,\Gamma_{t,r}\|u\|_2.\ }\tag{2}
\]
This single factor 2 avoids the factor 4 that generally arises from separately bounding \(\|A^t\|\|P_r[A]\|\). It also preserves cancellations that a coefficient-by-coefficient triangle bound discards. The factor 2 is sharp in the unrestricted complete theorem, as the two-by-two nilpotent \(A=\begin{pmatrix}0&2q\\0&0\end{pmatrix}\) and the scalar polynomial \(z\) show. Sharpness of (2) for the particular \(P_r\) is not claimed.

Define \(B_T=2\Gamma_{T,r}\|u\|_2\). Since \(q<1\) and
\(\Gamma_{t,r}\) is an upper bound obtained by maximizing
\(|z|^t|z-q|^r\) over the auxiliary radial interval \(0\le|z|\le q\),
the sequence \(\Gamma_{t,r}\) is nonincreasing; thus (2) implies
\(\|v_t\|\le B_T\) for all \(t\ge T\).

There is also a **late-pair refinement**. For distinct \(s,t\ge T\), assume \(s<t\). Apply complete Crouzeix *directly* to
\([z^s(1-z^{t-s})P_r(z)][A]\):
\[
\|v_s-v_t\|_2
\le 2\max_{z\in K}|z|^s|1-z^{t-s}|\|P_r(z)\|\|u\|
\le (1+q) B_T. \tag{3}
\]
The factor \(1+q<2\) comes from \(|z^{t-s}|\le q\), and the bound also holds for \(s=t\).

**General extension.** Replace \(C(z)\) by any \(m\times m\) polynomial \(C_m(z)\) satisfying \(\max_{z\in K}\|C_m(z)\|\le M\). Then (2) and (3) hold with \(M\Gamma_{t,r}\) in place of \(\Gamma_{t,r}\), independently of coefficient dimension \(m\). The columns may interact noncommutatively.

## 3. Refined Lp history compactification

Let \(1<p<\infty\), \(p\ne2\), \(D>1\), and \(T\ge1\). Realify the complex Hilbert tensor space; this preserves Euclidean distances. The normalized Gaussian map \(J(v)(g)=\langle g,v\rangle/(\mathbb E|G|^p)^{1/p}\) is an isometric embedding of that real Hilbert space into real \(L_p\). OpenAI Math #094 therefore gives, for the \(T+1\) points
\[
\{0,v_0,\ldots,v_{T-1}\},
\]
a (possibly nonlinear) map into \(\ell_p^d\) of distortion at most \(D\), with
\[
d\le\exp\bigl(C_{p,D}(\log(T+1))^{\gamma(p)}\bigr),
\quad
\gamma(p)=\begin{cases}2-p&1<p<2,\\1-2/p&p>2.\end{cases}
\]
Translate the image of zero to zero and absorb the common distortion scale. Call the observed images \(y_t\) and clip all \(t\ge T\) to the zero vector. Define
\[
E_T=\max_{s,t<T\text{ or one is anchor}}
\left|\|v_s-v_t\|_2-\|y_s-y_t\|_p\right|,
\quad
E_{0,T}=\max_{s<T}\left|\|v_s\|_2-\|y_s\|_p\right|.
\]

**Theorem B (all-horizon filtered orbit).** Every pair of observation times satisfies
\[
\boxed{\ 
\left|\|v_s-v_t\|_2-\|y^{\rm clipped}_s-y^{\rm clipped}_t\|_p\right|
\le
\max\{E_T,\ E_{0,T}+B_T,\ (1+q)B_T\}.
\ }\tag{4}
\]
The dimension is independent of the original state dimension and the polynomial's coefficient dimension. In particular \(E_{0,T}\le E_T\) and
\(E_T\le(D-1)\operatorname{diam}(\{0,v_0,\ldots,v_{T-1}\})\).
At fixed \(p,D,r,a,b\), the tail part of (4) decays as \(O(q^T T^{-r/2})\), while the measured finite-window distortion remains a separate term.

**Proof.** Both observed: error at most \(E_T\). One observed and one clipped: the reverse triangle inequality bounds the change in the original distance caused by replacing \(v_t\) by zero by \(\|v_t\|\le B_T\); the observed-to-anchor sketch error is at most \(E_{0,T}\). Both clipped: the sketch distance is zero, so apply (3). These cases give (4). The discrete generalization with an arbitrary independent late-pair budget \(L\) is kernel-checked in `MathCan/FilteredOrbit.lean`. \(\square\)

## 4. Exact synthetic numerical-range certificate and measured example

Set \(a=3/8\), \(b=1/2\), \(q=7/8\). Use 32 rational two-by-two Jordan blocks
\[
A_i=
\begin{pmatrix}a_i&b_i\\0&a_i\end{pmatrix},
\qquad
a_i=3/8-i/1024,\quad
b_i=1-2i/1024-((5i)\bmod7)/256.
\]
For each \(i\),
\(|a_i-a|+b_i/2\le b\); the \(i=0\) block has exact numerical range \(K=D(a,b)\). Consequently \(W(\mathrm{diag}(A_i))=K\) exactly. All containment checks use rational arithmetic. The nonnormal single-step gain is genuine: the first block has operator norm \(9/8\), although \(w(A)=7/8<1\). With two coefficient channels, the filtered Hilbert state has dimension \(64\times2=128\).

For \(r=2\), \(T=18\), and a seeded \(k=24\) Gaussian L4 sketch, the deterministic local reference gives:

| Quantity | Value |
| --- | ---: |
| Worst observed-pair error \(E_T\) | 0.019230627339 |
| Observed-to-anchor error \(E_{0,T}\) | 0.017641810799 |
| Curvature tail radius \(B_T\) | 0.007150104311 |
| Single-Crouzeix disk-only tail radius | 0.180790227001 |
| Coefficient-triangle tail radius | 1.038131381609 |
| Refined global budget \(\max(E_T,E_{0,T}+B_T,(1+q)B_T)\) | 0.024791915111 |
| Old loose budget \(E_T+2B_T\) | 0.033530835962 |
| Measured worst finite-probe error | 0.019230627339 |

The **curvature radius is approximately 25.28 times smaller** than the disk-only bound. This is a comparison of valid upper bounds, not a 25-fold measured capability improvement. The sampled sketch does not instantiate the unknown subpolynomial existential dimension constant from paper #094. The finite-probe distances and their last decimal digits are floating-point measurements; the exact disk inclusions and binomial-coefficient controls are rational.

Applied scripts, independent polynomial convolution oracle, exact rational-grid curvature tests, and CI: [Compactification-Theory NOR-02](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor01-numerical-orbit-sketch-20261115/research/nor01_numerical_orbit_sketch).

## 5. Open verification gates

1. Export a trained looped transformer's real Jacobian over pre-registered hidden-state trajectories and certify a disk (or other exposed radial geometry) that contains its **complex numerical range**. Singular-value, spectral-radius and sampling-only bounds are distinct certificates.
2. Evaluate matrix-valued temporal readouts with measured \(E_T,E_{0,T}\), under held-out recurrence depths. Check whether the deterministic linearization error is bounded; without this, (4) applies only to the linearized surrogate.
3. Construct an explicit low-dimension \(L_p\) embedding with independently measured distortion, and compare it to a random Gaussian sketch. Paper #094's existence theorem does not give a general efficient algorithm.
4. Formalize Theorem A's real/complex geometry and Theorem B's functional-calculus assumptions in Lean with appropriate analytic libraries. The current Lean module intentionally covers the discrete stitching boundary only.

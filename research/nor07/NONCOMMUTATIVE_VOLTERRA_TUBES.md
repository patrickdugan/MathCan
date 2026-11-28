# NOR-07T: cancellation-preserving Volterra tubes for nonlinear recurrent maps

**Status:** new mathematical derivation with a written analytic proof and a separate Init-only Lean proof of the noncommutative ordered-product identity. Applied status depends on the source-locked [NOR-07 trained-GRU branch](https://github.com/MoralityLabAI/Compactification-Theory/pull/148) and its rational CI receipt. Priority over previous literature is unverified.

## 1. Recentered nominal dynamics

Let \(F:U\to U\) be a \(C^2\) map on a convex invariant subset \(U\) of a real Hilbert space \(H\), and suppose
\[
\|D^2F(z)[u,v]\|\le M\|u\|\|v\|\quad(z\in U).
\]
Choose nominal centers \(c_0,\ldots,c_L\) and nominal bounded linear operators \(B_0,\ldots,B_{L-1}\). An external rational interval oracle must establish
\[
\|F(c_j)-c_{j+1}\|\le e_j,\qquad
\|DF(c_j)-B_j\|\le\eta_j.
\]
Define the **time-ordered products** \(P_{j,k}=B_{j-1}\cdots B_k\), with \(P_{j,j}=I\). Assume nonnegative \(s_{j,k}\ge\|P_{j,k}\|\), and fix a starting radius \(r\).

**Theorem A (nonlinear trajectory tube).** Set \(\delta_0=r\), and for \(j\ge1\) define
\[
\boxed{
\delta_j=s_{j,0}r+
 \sum_{k=0}^{j-1}s_{j,k+1}
 \left(e_k+\eta_k\delta_k+\frac M2\delta_k^2\right).
}\tag{1}
\]
For every \(x_0\in B(c_0,r)\), the actual nonlinear trajectory \(x_j=F^j(x_0)\) satisfies \(\|x_j-c_j\|\le\delta_j\), provided the line segments between each \(x_j\) and \(c_j\) lie in \(U\).

*Proof.* Taylor's integral formula writes
\[
x_{k+1}-c_{k+1}
=B_k(x_k-c_k)+w_k,\qquad
\|w_k\|\le e_k+\eta_k\|x_k-c_k\|
+\frac M2\|x_k-c_k\|^2 .
\]
Unrolling the exact noncommutative recurrence gives
\[
x_j-c_j=P_{j,0}(x_0-c_0)
+\sum_{k<j}P_{j,k+1}w_k.
\]
Apply the norm bounds and induction on \(j\) to obtain (1). The formula preserves cancellations in each nominal contiguous product \(P_{j,k}\). \(\square\)

## 2. Uniform block-derivative certificate

Write \(A_j=D(F^j)(x_0)\), \(P_j=P_{j,0}\), and let
\(\varepsilon_k=\eta_k+M\delta_k\). Define \(E_0=0\) and
\[
\boxed{
E_j=\sum_{k<j}s_{j,k+1}\varepsilon_k
                  (s_{k,0}+E_k).
}\tag{2}
\]

**Theorem B (ordered Jacobian-product enclosure).** Uniformly for \(x_0\in B(c_0,r)\),
\[
\|A_j-P_j\|\le E_j,\qquad
\boxed{\|D(F^L)(x_0)\|\le s_{L,0}+E_L.}\tag{3}
\]
For an independent center-residual computation, evaluate (1) with \(r=0\). If the resulting value is \(\delta_L^{(0)}\), then
\[
\|F^L(c_0)-c_0\|
\le \|c_L-c_0\|+\delta_L^{(0)}.\tag{4}
\]

*Proof.* For each \(k\), by the Hessian bound,
\(\|DF(x_k)-B_k\|\le\eta_k+M\|x_k-c_k\|\le\varepsilon_k\).
The exact *noncommutative Volterra product identity* is
\[
A_j-P_j=
\sum_{k<j}P_{j,k+1}
    \left(DF(x_k)-B_k\right)A_k.\tag{5}
\]
It follows from ordered-product telescoping, without commuting any adjacent matrices. Taking norms and using \(\|A_k\|\le s_{k,0}+E_k\), induction gives (2)–(3). Formula (4) is Theorem A applied to the exact nominal starting point. \(\square\)

**Theorem C (validated local nonlinear contraction).** Let \(G=F^L\) and \(R>0\). If the rational computations certify
\[
K:=s_{L,0}+E_L<1,\qquad
\|c_L-c_0\|+\delta_L^{(0)}+KR<R,
\]
then the whole closed ball \(B(c_0,R)\) is mapped into itself by the *actual nonlinear* \(G\), and has a unique \(G\)-fixed point. The NOR-05 one-step return criterion may subsequently establish period-one status for \(F\).

### Cancellation that a one-step-norm product loses

For \(B=\begin{pmatrix}0&3\\0&0\end{pmatrix}\), we have \(\|B\|_2=3\) while \(B^2=0\). Thus the product-of-one-step-norms estimate at two steps is \(9\), while the true nominal product norm is zero. Real trained GRU Jacobians are not nilpotent but can be similarly nonnormal. Retaining \(s_{j,k}=\|P_{j,k}\|\) rather than using \(\prod_{\ell=k}^{j-1}\|B_\ell\|\) is the key structural improvement.

The supplied certificate can use rational midpoint Jacobians and upward rational Frobenius norm bounds as its \(s_{j,k}\). These are sufficient for the true complex numerical range when passed through a separate Hilbert norm envelope, and they do not assume that a real nonsymmetric matrix is normal.

## 3. Lean scope

[The formal module](../../MathCan/NOR07Volterra.lean) defines the ordered product over **any semiring**, hence in particular for noncommuting matrix semirings. Its exact algebraic theorem proves
\[
\prod_{j=0}^{L-1}(B_j+Q_j)
=\prod_{j=0}^{L-1}B_j+
\mathsf{Correction}_L
\]
with the recursion
\(\mathsf{Correction}_{n+1}=B_n\mathsf{Correction}_n
+Q_n\prod_{k=0}^{n-1}(B_k+Q_k)\).
This is the algebraic core of (5); the analytic norm estimates, Taylor theorem and fixed-point theory are human-readable proofs, not Lean formalizations.

## 4. Application and limitations

The companion [NOR-07T Python certificate](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/nor07-rrc25-two-attractors-20261115/research/nor01_numerical_orbit_sketch/nor07_recentered_tube.py) uses the original 1,000-parameter RRC-25 trained GRU, exact rational checkpoint decimals, a global analytic Hessian bound on the invariant hidden-state cube, and outward-rounded rational sigmoid/tanh intervals. It verifies (1)–(4) with a 24-step nominal Jacobian sequence around the independent squared-family candidate, retaining full product matrices. A passed CI receipt may certify a second attracting fixed point. The squared-family *input orbit's entry* into the tiny fixed-point ball is a distinct NOR-06 capture obligation.

The result relates to OpenAI Math #094 through the conditional all-depth nonlinear orbit metric embeddings of NOR-04–07 and to #325 through matrix-valued polynomial control on certified frozen derivatives. The new Volterra tube proof itself requires standard Taylor calculus and finite-dimensional operator-norm properties.

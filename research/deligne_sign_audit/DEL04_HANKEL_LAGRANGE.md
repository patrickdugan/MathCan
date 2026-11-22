# DEL-04: Hankel formalization and Lagrange extraction

Source: [Hexagon 2611.00789v1](https://hexagonmath.org/2611.00789v1),
Lemma 2. Builds on MathCan DEL-01, DEL-02 and DEL-03.
Date: 22 November 2026.

## Status and separation of obligations

The isolated Lean/Mathlib 4.35 experiment at
`experiments/deligne_mathlib/` targets the generic weighted moment
matrix and a scalar geometric-growth lemma. Code under
`research/deligne_sign_audit/lagrange_isolation.py`
independently checks rational instances of the general polynomial identity.

A formal statement is certified only when the dedicated DEL-04 workflow
passes and `#print axioms` has no `sorryAx` or `ofReduceBool`.
These developments concern **Lemma 2**, not Deligne's geometric theorem.

## 1. General Hankel determinant

Let \(R\) be a commutative ring, let \(\lambda_j,m_j\in R\)
for \(j=0,\ldots,s-1\), and set

\[
t_n = \sum_j m_j \lambda_j^n,\quad
H_{ab}=t_{a+b+1},\quad
V_{ja}=\lambda_j^a.
\]

There is an equality of matrices, not merely a determinant relation:

\[
H=V^{\mathrm T}\operatorname{diag}(m_j\lambda_j)V.
\]

Taking determinants and applying the Vandermonde formula gives

\[
\det H
=\left(\prod_jm_j\lambda_j\right)
  \prod_{i<j}(\lambda_j-\lambda_i)^2.
\]

Over an integral domain, if all \(m_j,\lambda_j\) are nonzero
and \(\lambda\) is injective, then \(\det H\ne0\). No positivity,
convergence, algebraic closure or characteristic-zero hypothesis
is required for the **determinant formula**.

Over characteristic zero, the eigenvalues can be regarded as distinct
nonzero complex numbers, with positive integer algebraic
multiplicities after equal eigenvalues are aggregated.

## 2. A finite polynomial isolator

Fix \(i\), and let

\[
Q_i(X)=\prod_{j\ne i}(X-\lambda_j)=
      \sum_{r=0}^{s-1}c_{i,r}X^r.
\]

Every other eigenvalue is a root of \(Q_i\), while
\(Q_i(\lambda_i)=\prod_{j\ne i}(\lambda_i-\lambda_j)\ne0\).
For every positive integer \(n\),

\[
\begin{aligned}
\sum_{r=0}^{s-1}c_{i,r}t_{n+r}
&=\sum_jm_j\lambda_j^nQ_i(\lambda_j)\\
&=m_i\lambda_i^nQ_i(\lambda_i).
\end{aligned}
\]

This is a fixed finite linear combination of consecutive power traces
whose coefficients depend on the spectrum but are **independent of n**.
The Python witness evaluates both sides in exact rational arithmetic.

This polynomial identity can replace the complex generating-function
pole argument in a formal proof of the spectral bound.

## 3. All-powers growth implication

Let \(B>0\), \(C\ge0\), and suppose
\(|t_n|\le CB^n\) for all \(n\ge1\). Then

\[
|m_iQ_i(\lambda_i)|\,|\lambda_i|^n
\le C B^n\sum_{r=0}^{s-1}|c_{i,r}|B^r.
\]

The coefficient on the left is nonzero, so a constant \(C_i\)
gives \(|\lambda_i|^n\le C_iB^n\).
If \(|\lambda_i|>B\), the positive real number
\(|\lambda_i|/B>1\) has unbounded integer powers. Thus
\(|\lambda_i|\le B\).

For \(B=0\), a uniform bound forces every positive power trace
to vanish. The same isolator identity with \(n=1\) would give
\(m_i\lambda_iQ_i(\lambda_i)=0\), impossible with the
nonzero assumptions. The positive-base case is the main
form needed for the paper, since \(B\) is a positive power of \(q\).

This elementary proof uses the all-powers hypothesis and works
for any finite complex spectrum with distinct, nonzero eigenvalues
and nonzero aggregated coefficients. Positivity is a natural
sufficient condition for the algebraic weights of a genuine
Frobenius module.

## 4. What remains for full Lemma 2

The formal dependencies are:

- Generic Hankel factorization and nonvanishing in Mathlib.
- Generic polynomial isolator existence and its finite trace identity.
- A bound on the finite linear combination of trace windows, via
  triangle inequality and \(\lvert t_{n+r}\rvert\le CB^{n+r}\).
- Real geometric growth, followed by the \(k\)-th-root limit with
  the actual varying \(e_k,c_k\) quantified as in Lemma 2.

The test suite checks isolation on 112 seeded rational spectra
with 1-8 distinct eigenvalues, plus duplicates and adversarial
virtual cancellation. These are exact examples and do not
themselves certify the general complex norm inequality.

Separate geometric obligations still include weak Lefschetz,
Poincaré duality, Gysin exactness, Frobenius equivariance,
and the trace-identification of the hypersurface remainder.

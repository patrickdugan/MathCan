# DEL-03: exact power-sum Hankel certificates

**Target:** Hexagon 2611.00789v1, Section 3, Lemma 2.
**Scope:** a genuine algebraic identity over characteristic-zero fields,
exercised with exact rational arithmetic. The analytic radius-of-convergence
argument and the tensor-power limit remain external mathematical obligations.

## Algebraic identity

Let the distinct nonzero eigenvalues be \(\lambda_1,\dots,\lambda_s\),
with nonzero aggregated multiplicities \(m_1,\dots,m_s\).
Write the power traces as

\[
t_n=\sum_{j=1}^s m_j\lambda_j^n,\qquad n\ge1.
\]

The \(s\times s\) Hankel matrix \(H_{ab}=t_{a+b+1}\), for
\(0\le a,b<s\), factors as

\[
H=V\operatorname{diag}(m_j\lambda_j)V^T,
\qquad V_{aj}=\lambda_j^a.
\]

Consequently

\[
\boxed{\det H=\left(\prod_j m_j\lambda_j\right)
                 \prod_{i<j}(\lambda_j-\lambda_i)^2}.
\]

The identity holds over characteristic-zero fields. Genuine algebraic
multiplicities have \(m_j>0\). With \(\lambda_j\ne0\) and distinctness,
the determinant is nonzero, so the full set of \(s\) spectral poles is
present in the trace sequence.

The trace generating function is

\[
G(z)=\sum_{n\ge1}t_nz^n
    =\sum_j m_j\frac{\lambda_j z}{1-\lambda_j z},
\]

with pole coefficient

\[
\lim_{z\to1/\lambda_j}(1-\lambda_j z)G(z)=m_j.
\]

Every reciprocal eigenvalue is a nonremovable pole when its aggregated
multiplicity is nonzero. Positivity is sufficient; signed virtual
trace differences can cancel equal eigenvalues and erase a pole.

The degree-s monic polynomial \(P(X)=\prod_j(X-\lambda_j)\)
satisfies the trace recurrence. Once s is known, the first 2s
power traces uniquely determine its coefficients through the
invertible Hankel system.

## Relation to Lemma 2

For each fixed k, the genuine Frobenius module
\(V^{\otimes k}\oplus K_k\) has positive multiplicities.
The algebraic result above explains why its poles do not cancel.

The remaining step is analytic. The uniform all-powers bound
\(|t_n|\le C B^n\) makes the generating function holomorphic
for \(|z|<1/B\), hence each nonremovable pole must lie outside
that disc. Lemma 2 then takes k-th roots and uses
\(c_k/k\to0\). This part is sourced to the paper and
remains unformalized in this code.

## Executable checks and training

The new power_sum_poles.py uses only fractions.Fraction to
compute traces, Hankel matrices, Vandermonde products, pole
coefficients, and exact monic recurrence recovery.

Regression tests cover 98 seeded rational spectra of 1-7
distinct eigenvalues; repeated positive multiplicities;
eigenvalues 7 and -7, whose first power trace vanishes but
whose second trace is 98; and the virtual difference
\(7^n-7^n+3^n\), in which the eigenvalue 7 disappears.

This exact rational component supplies verifier-grounded proof-repair
tasks. The determinant identity is general mathematics, and the
current oracle checks finite rational cases. It is not a Lean proof.

Next Lean/Mathlib target: factor the Hankel matrix as a Vandermonde
product, derive the determinant, then formalize the analytic
all-powers growth argument. The étale/Gysin prerequisites remain
separate from this module.

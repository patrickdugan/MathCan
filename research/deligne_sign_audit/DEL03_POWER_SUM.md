# DEL-03: exact power-sum Hankel certificates

**Target:** Hexagon 2611.00789v1, Section 3, Lemma 2.
**Scope:** a genuine algebraic identity over characteristic-zero fields,
exercised with exact rational arithmetic. The analytic radius-of-convergence
argument and the tensor-power limit remain external mathematical obligations.

## Algebraic identity

Let the distinct nonzero eigenvalues be $`\lambda_1,\dots,\lambda_s`$, with nonzero aggregated multiplicities $`m_1,\dots,m_s`$. Write the power traces as

```math
t_n=\sum_{j=1}^s m_j\lambda_j^n,\qquad n\ge1.
```

The $`s\times s`$ Hankel matrix $`H_{ab}=t_{a+b+1}`$, for $`0\le a,b<s`$, factors as

```math
H=V\,\mathrm{diag}(m_j\lambda_j)V^T,
\qquad V_{aj}=\lambda_j^a.
```

Consequently

```math
\boxed{\det H=\left(\prod_j m_j\lambda_j\right)
                 \prod_{i\lt j}(\lambda_j-\lambda_i)^2}.
```

The identity holds over characteristic-zero fields. Genuine algebraic multiplicities have $`m_j>0`$. With $`\lambda_j\ne0`$ and distinctness, the determinant is nonzero, so the full set of $`s`$ spectral poles is present in the trace sequence.

The trace generating function is

```math
G(z)=\sum_{n\ge1}t_nz^n
    =\sum_j m_j\frac{\lambda_j z}{1-\lambda_j z},
```

with pole coefficient

```math
\lim_{z\to1/\lambda_j}(1-\lambda_j z)G(z)=m_j.
```

Every reciprocal eigenvalue is a nonremovable pole when its aggregated
multiplicity is nonzero. Positivity is sufficient; signed virtual
trace differences can cancel equal eigenvalues and erase a pole.

The degree-s monic polynomial $`P(X)=\prod_j(X-\lambda_j)`$ satisfies the trace recurrence. Once s is known, the first 2s power traces uniquely determine its coefficients through the invertible Hankel system.

At $p=3$, the eight Dirichlet characters in Lee Crossley’s 547/727 example have local Euler denominator $(1-T^4)^2$. The four eigenvalues $1,-1,i,-i$ each occur twice, giving $(t_1,\ldots,t_8)=(0,0,0,8,0,0,0,8)$. The Hankel matrix has 8 on its antidiagonal and zero elsewhere, so $\det H=4096$ and the recovered polynomial is $X^4-1$. The trace generating function $G(z)=8z^4/(1-z^4)$ has a simple pole at each fourth root of unity. The local Euler factor has a double pole at each of those points. [Euler factors, order-four case](https://github.com/leecrossley/theta-race-finite-euler-readout/blob/b01619cac6e661a66587a45af435413592d368d0/PROOF.md#L53-L61) ([DOI](https://doi.org/10.5281/zenodo.24413208)).

## Relation to Lemma 2

For each fixed k, the genuine Frobenius module $`V^{\otimes k}\oplus K_k`$ has positive multiplicities. The algebraic result above explains why its poles do not cancel.

The remaining step is analytic. The uniform all-powers bound $`|t_n|\le C B^n`$ makes the generating function holomorphic for $`|z|<1/B`$, hence each nonremovable pole must lie outside that disc. Lemma 2 then takes k-th roots and uses $`c_k/k\to0`$. This part is sourced to the paper and remains unformalised in this code.

## Executable checks and training

The new power_sum_poles.py uses only fractions.Fraction to
compute traces, Hankel matrices, Vandermonde products, pole
coefficients, and exact monic recurrence recovery.

Regression tests cover 98 seeded rational spectra of one to seven distinct eigenvalues and repeated positive multiplicities. For eigenvalues 7 and −7 the first power trace vanishes and the second equals 98. The tests also cover the virtual difference $`7^n-7^n+3^n`$, in which the eigenvalue 7 disappears.

This exact rational component supplies verifier-grounded proof-repair
tasks. The determinant identity is general mathematics, and the
current oracle checks finite rational cases. It is not a Lean proof.

Next Lean/Mathlib target: factor the Hankel matrix as a Vandermonde
product, derive the determinant, then formalize the analytic
all-powers growth argument. The étale/Gysin prerequisites remain
separate from this module.

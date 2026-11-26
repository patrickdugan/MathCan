# Independent FLINT certificate replay

Run a complete replay with:

```bash
python3 flint_replay.py symbolic_results/certificate31.json \
  --expected-order 31 --output receipts/flint_replay31.json
```

The command reconstructs every residue equation, then calls `symbolic_norm_replay.replay` to recompute the norms, integer identity and exceptional fibres. A receipt obtains `status: passed` after both parts succeed against the same certificate SHA256. The receipt records hashes of the checker, generic recurrence module, elimination checker and written residue proof.

## Independent residue calculation

The search computed its residue coefficients with a translation recurrence in PARI. This checker instead derives the local Laurent expansion from the distinct roots of the kernel polynomial, using FLINT integer multivariate polynomials.

Write $v_i=2y_i+a_1x_i+a_3$, $w_i=6x_i^2+b_2x_i+b_4$, and

$$
S_i=\sum_{j\ne i}\frac1{x_i-x_j},\qquad
T_i=\sum_{j<k,\ j,k\ne i}\frac1{(x_i-x_j)(x_i-x_k)}.
$$

The local coefficients of $1/\Phi(x)$ are

$$
a_i=-v_iS_i-\frac{w_i}{2v_i},\qquad
b_i=a_i^2-2x_i-\frac{b_2}{6}-w_iS_i-v_i^2T_i.
$$

Here the local parameter comes from the associated short equation at its identity, and is translated to each subgroup point. In Tate coordinates the pole coordinate has constant term $-b_2/12$, so the residue theorem gives

$$
u_i=b_i-b_2/12.
$$

Consequently the two fixed shifts disappear from $u_i-u_1$. The checker omits $b_2/6$ when constructing each $b_i$ and compares the resulting difference with the stored $g_i/d_i$.

The generic coordinate fractions and local expansions are kept in the fraction field of $\mathbb Z[r,t]$. Gcd cancellation takes place before specializing to the order equation. For every asserted equality, the checker cross-multiplies the integer numerators and denominators and computes the remainder modulo the independently reconstructed monic order polynomial. The accepted remainder is exactly zero. This avoids the large intermediate expressions produced by repeatedly inverting elements in the rank-fourteen or rank-sixteen quotient algebra.

## Denominators and specialization

The input coordinate denominators arise from the stated addition recurrence. They remain nonzero on its specified open locus. Extra reciprocals occur only for $x_i-x_j$ and $v_i$, together with the scalar two. Distinct nonidentity pairs of points have distinct $x$-coordinates. The equality $v_i=0$ would make $iT$ a point of order two, which an odd-order subgroup cannot contain.

Each cancelled polynomial gcd divides a denominator already known to be nonzero on this locus. Its value is therefore nonzero there, including in finite characteristic. The normalized denominators still consist of units on the same locus. No division by an untracked integer or modular-chart element enters the final remainder check. The only scalar division in the difference formula is by two; the displayed constant shift disappears before comparison.

The stored denominators $t^a(t-1)^b$ receive explicit nonnegative-integer exponent checks. Both $t$ and $t-1$ are units on the smooth marked-order locus. The generic order-polynomial reconstruction checks that its remaining discarded factors are among $r,r-1,t,t-1$ and that its integer unit is $1$ or $-1$.

## Elimination and exceptional fibres

After the residue calculation, the separate checker recomputes each exact resultant, verifies the integer Bezout identity, and accounts for every prime divisor of its integer. Over each surviving characteristic it verifies the irreducible factorization of the common polynomial in $t$, then recomputes the fibre gcd in $r$ over the specified residue field. Divisibility of a power of the discriminant by that gcd proves that all its geometric roots are singular.

The mathematical link from the local Laurent coefficients to the matrix obstruction is the residue theorem proved in `uniform_probe.md`. This replay does not enumerate the full symbolic matrix product $H\lambda$. Its exact arithmetic supplies an independent check of the same residue-ratio identities. The written geometry remains a dependency of the complete exclusion argument.

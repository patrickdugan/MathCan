# Graham–Carrot investigation 02

## Established mathematics

For every integer `m>=1`, write `N=3^m` and
`F_N(X)=X^N-4`, `G_N(X)=X^N-2`.

**Theorem 1 (irreducibility).** Both polynomials are irreducible over the rationals.

Proof: modulo 7, both constants 2 and 4 are noncubes. For `N=3^m`, the finite-field binomial irreducibility criterion gives irreducibility of `X^N-a` in `F_7[X]` when `a` is a noncube. Gauss's lemma lifts irreducibility to `Q[X]`.

**Theorem 2 (admissibility).** For any prime `p`, some integer `x` satisfies `p ∤ F_N(x)G_N(x)`.

Proof: when `p` is odd, `x=0` gives product 8. For `p=2`, `x=1` gives product 3.

**Theorem 3 (root counts).** For odd prime `p`, put `d=gcd(N,p-1)`. Let `nu_p` denote the number of roots of `F_N(x)G_N(x)` modulo `p`. Then `nu_p=2d` if `pow(2,(p-1)/d,p)==1`, and `nu_p=0` otherwise. Also `nu_2=1`.

Reason: the image of the `N`th-power map has odd-index gcd parameter `d`, a power of 3. Squaring is an automorphism of the relevant quotient, so 2 and 4 are either both `N`th powers or neither. Each nonzero target has exactly `d` preimages. Their preimages are disjoint.

**Theorem 4 (spectral sieve).** With `M_H=prod_{p<=H}p`, let `w_H(n)=1[gcd(n,M_H)=1]` and `delta_H=phi(M_H)/M_H`. Then
`R_H(h)=prod_{p<=H}(1-(2-1[p|h])/p)`.
In particular,
`S_H=R_H(2)/delta_H^2=2 prod_{3<=p<=H}(1-(p-1)^(-2))`,
and for integer `H>=2`, `(1-1/H) S_H <= 2 C_2 <= S_H`.

**Theorem 5 (perfect powers).** For integers `a,m>=2`, both `a^m-1` and `a^m+1` are prime if and only if `a=m=2`. The negative-side factorization forces `a=2` and `m` prime; the positive side forces `m` a power of two.

## Conjectural boundary

For fixed `m`, Bateman–Horn predicts
`#{2<=x<=X: F_N(x),G_N(x) prime} ~ (mathfrak S_N/N^2) X/(log X)^2`.
Here `mathfrak S_N=prod_p (1-nu_p/p)/(1-1/p)^2`.
Admissibility makes local factors positive but does not prove infinitely many integer prime pairs.

## Numerical agenda

The accompanying stdlib Python program verifies root counts, counts candidate twin pairs, and calculates truncated Euler products. These finite computations are tagged CHECKED, never a proof of Bateman–Horn. New calculations should record Python version, ranges, exact primality method, cutoff and commit SHA.

## Larger mathematical questions

- For fixed `H`, how rapidly do local root counts stabilize as `m` increases? Answer: once `m>=max_{p<=H} v_3(p-1)`.
- Does the whole singular series admit useful estimates uniform in `m`? Open.
- Can short-interval information about twin-prime lower members make a fixed rounded-exponent sequence into a theorem? Conditional on strong, presently unavailable gap control.
- Can Liouville-twisted sums be uniformly controlled along a growing sieve cutoff? This is closely tied to the parity barrier.

## References to consult

- Hardy & Littlewood, *Some problems of 'Partitio numerorum', III*, 1923.
- Bateman & Horn, *A heuristic asymptotic formula concerning the distribution of prime numbers*, 1962.
- R. Lidl and H. Niederreiter, *Finite Fields*, binomial irreducibility criterion.
- Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point correlations*, 2015.
- Saito and Takeda, work on generalized Mills constants and prime-representing powers.

The 2026-10-28 conversation provided Investigation 01 as a narrative report, rather than an attached test artifact. Its claimed test counts remain unverified by this repository.

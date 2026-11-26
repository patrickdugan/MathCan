# Review of the independent FLINT certificate replay

The complete replay combines `flint_replay.py` with `symbolic_norm_replay.py`. A receipt reaches `status: passed` only after both components succeed on the same certificate hash. The earlier norm-only receipts establish elimination for their stored equations; complete receipts additionally verify that those equations represent the interpolation obstruction.

## Reconstruction of the obstruction

The checker independently derives the generic Tate coordinates from the addition recurrence using exact integer polynomial fractions. It reconstructs the marked-order factor and checks the removed factors against the open chart. The generic fraction implementation checks every gcd cancellation and permits only unit integer normalization scalars.

For a kernel root `x_i`, put `v_i=2*y_i+a1*x_i+a3`. Let `s1` be the sum of reciprocal differences `1/(x_i-x_j)` for `j!=i`, and let `s2` be the sum of their pairwise products. The checker derives these quantities directly from the coordinate list. In the translated parameter obtained from short Weierstrass coordinates,

```
x' = v,
x'' = 6*x^2+b2*x+b4,
x'''/(6*x') = 2*x+b2/6.
```

Expanding the product defining `Phi(x)` and then taking its reciprocal gives

```
a_i = -v_i*s1-x''_i/(2*v_i),
b_i = a_i^2-(2*x_i+b2/6)-x''_i*s1-v_i^2*s2.
```

The implemented coefficient omits the common term `-b2/6`. Differences of coefficients are therefore unchanged. The coordinate shift to the short model also matters when applying the residue theorem: in Tate coordinates, the Laurent expansion of `x` at the identity has constant term `-b2/12`. Hence the individual ratio is `u_i=b_i-b2/12`. Both constants disappear from `u_i-u_1`, exactly the quantity the checker compares with each stored `g_i/den_i`.

Each comparison clears its denominators and checks a zero polynomial remainder modulo the independently reconstructed order equation over the integers. It also checks the structural residue identity separately. This reconstruction uses the proved residue theorem; it does not use the search program's logarithmic-cocycle calculation to obtain the stored numerators.

## Denominators and specialization

Every coordinate recurrence denominator is nonzero on a smooth subgroup of the specified exact odd order. Later divisions occur only by two, by `x_i-x_j` for different representatives modulo negation, and by `v_i`. Distinct representatives have distinct coordinates, and `v_i` is nonzero because the point is not of order two. The characteristic assumption is greater than three.

All subsequent polynomial gcd cancellations occur over the integers. A cancelled factor divides an existing denominator whose value is nonzero at every admissible point. Its value must consequently be nonzero too. This reasoning covers integer-content factors as well as nonconstant factors, so cancellation does not silently discard a surviving characteristic. The stored powers of `t` and `t-1` are separately checked against the reconstructed rational function, and these factors belong to the marked-order open chart.

## Elimination and every exceptional characteristic

The second component recomputes each resultant of the marked-order equation with a stored numerator. It checks the complete equality with the claimed norm, including the powers removed at `t=0` and `t=1`. The integral Bezout sum is then compared with the stored positive integer `n0`.

Each listed characteristic is checked to be prime with exact integer arithmetic, and its full power is divided out of `n0`. The final remaining integer must be one. Thus the list accounts for every prime divisor of the certificate integer.

In each such characteristic, the checker recomputes the common univariate gcd of all norm polynomials and verifies its complete factorization into the supplied monic irreducibles. Over each associated residue field, it reconstructs the fibre gcd of the order polynomial and all obstruction numerators. Equality with every supplied coefficient is checked.

For that monic gcd `Gamma`, it verifies

```
Gamma divides Delta^max(1,degree(Gamma)).
```

This is equivalent to every geometric root of `Gamma` being singular. The exponent covers repeated roots, including inseparable multiplicities; no explicit splitting field is needed. A constant gcd represents an empty fibre. The argument therefore accounts for extension-field points as well as rational points.

## Focused negative controls

`symbolic_norm_controls.py` checks an intact order-19 elimination certificate and rejects nine changes, including an altered norm, Bezout cofactor, integer constant, omitted characteristic and altered fibre data.

`test_flint_bridge.py` checks a complete intact order-19 replay and then changes the first residue numerator and its power of `t` in separate copies. Both changes must fail at the direct Laurent-coefficient comparison. The denominator test is essential because an elimination-only verifier operates on the numerators. The receipt `audit_flint_bridge.json` records both rejections and confirms that the original files' hashes remained unchanged.

## How to describe the results

An order whose complete receipt has `status: passed`, with matching certificate and current source hashes, has an independently replayed interpolation exclusion relative to the written residue and chart lemmas. An order with only a successful elimination receipt has a verified zero-locus calculation for its stored numerators; the residue bridge remains an explicit obligation until its complete replay finishes. Neither receipt is a formal kernel proof of the algebraic geometry. The uniform theorem is separately supported by its written cocycle proof and Lean coefficient classification.

The final local runs completed for all four requested orders. `audit_replay_receipts.json` independently binds the completed receipts to the current certificate files and all recorded replay sources. It also checks the number of residue identities and norms, the embedded elimination status and the singularity conclusion for every listed fibre.

| Order | Residue identities | Recomputed norms | Complete replay seconds |
|---:|---:|---:|---:|
| 19 | 8 | 8 | 1.10 |
| 23 | 10 | 10 | 6.99 |
| 29 | 13 | 13 | 199.52 |
| 31 | 14 | 14 | 572.51 |

The earlier direct Node failures at the larger orders remain failed runs. These complete FLINT replays provide the separate successful route, with its geometric dependency stated above.

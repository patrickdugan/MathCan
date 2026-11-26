# TRR-10 proof review

## Endpoint and definitions

`tame_polynomialDecoder_degree_iff` quantifies over an actual
`MvPolynomial (Fin 4) K`. `BlockDegreeLE d D` requires every exponent in
`D.support` to satisfy `e 0 + e 1 <= d` and `e 2 + e 3 <= d`. Thus the degree
model is ordinary total degree in each coordinate pair.

`PolynomialDecoderOn H u D` quantifies over nonidentity points `P,Q` of the
actual subgroup `H`. The evaluated polynomial equals `assignedX u (P+Q)`.
`assignedX` uses the ordinary affine x-coordinate at finite points and the
specified `u` at the group identity. The formal statement places no affine
coordinate constraint on the identity input, which is outside the domain.

The final iff assumes a smooth short model over a field, finite odd order
`N >= 19`, and nonzero images of `2`, `3`, and `N` in that field. It carries
no remaining residue, moment or interpolation premise. A decidable equality
instance is used to form finite polynomial expressions. Classical choice
supplies that interface for any field.

## Lower bound

`RootCardinality` proves that each nonidentity x-fibre contains precisely
`P` and `-P`, then counts the roots. `ResidueAnnihilation` pairs these points
inside the actual finite subgroup sum. The x-only contribution cancels;
the y-part becomes the finite barycentric sum on the distinct x-roots.

Mathlib's finite Lagrange identity identifies that sum with the coefficient
of degree `m-1`. The coefficient vanishes below that degree. In
`ResidueMonomials`, the curve equation supplies the even or odd normal form
of each monomial. The weight inequality `2a+3b <= N-1` gives the required
strict degree bound in the odd case.

`BlockPolynomial` expands an actual four-variable polynomial over its
support. Since each second-block monomial has `a+b <= d`, `3d <= N-1`
supplies the residue moment for that term. Finite distributivity then
annihilates each evaluated row.

`assignedX_residue_row` handles the identity value explicitly. Only the
index `Q=-P` contributes the assignment, and oddness of the residue makes
that contribution `-u*lambda(P)`. This proves the exact eigenvector premise
of TRR-09 from the decoder definition. Its checked exclusion yields the
ordinary-degree lower bound.

## Upper bound

`PolynomialLift` replaces each power `x^j` by the actual polynomial
`X^(j%3)*(Y^2-A*X-B)^(j/3)`. The source proves both evaluation on the cubic
and ordinary total-degree bounds. Terms multiplied by `Y` use the bound
`2j+3 <= 3d`.

`PointInterpolation` applies this lift to the two parts of
`beta_P(x)*(1/2+y/(2*y(P)))`, where `beta_P` is the actual Lagrange basis on
the distinct x-roots. Equal x-coordinates identify a point with `P` or `-P`.
The sign factor separates those two cases, while the Lagrange factor
annihilates every other fibre. Nonzero tangent denominators justify the
division by `2*y(P)`.

The basis degree is at most `m-1`. Its odd part has weight at most
`2(m-1)+3=N`, so `N <= 3d` gives ordinary degree at most `d` after lifting.
`BlockTensor` constructs the four-variable polynomial by a literal finite
sum of monomials. It proves both the block support bound and evaluation of
the target matrix.

The upper theorem needs finite subgroup cardinality, absence of nonzero
two-torsion, and `2 != 0` in the field. The stronger tame assumptions enter
through the lower bound when `DecoderDegree` proves the iff.

## Audit

The verifier's explicit declaration contract contains 180 reports: the
113 inherited reports and 67 new reports. All 27 audited sources are
compiled directly after the aggregate build. Raw source guards and the
axiom parser are inherited from the frozen earlier verifiers. The allowed
transitive dependencies remain `propext`, `Classical.choice`, `Quot.sound`.

The source versions and dependencies are hashed in the receipt. Each
mathematical mutation must trigger a compiler error within the changed
theorem, so an import failure cannot satisfy a rejection control. The
off-by-one mutation exposes the weight `N` boundary, and the sign mutation
tests the assigned identity term in the actual model.

The finite arithmetic sweep checks the same formulas through independent
coefficient dictionaries and modular elimination. It includes matching
characteristic and small orders for the identities and upper construction.
Those finite cases do not extend the hypotheses of the universal lower
bound. Full coefficient witnesses permit independent evaluation of the
106 decoder fixtures.

## Remaining obligations

The next formal work concerns generalized-coordinate transfer, the lower
bound when the characteristic divides the marked order, and the small-order
certificate interfaces. The universal exact-degree theorem already covers
finite extensions and all odd composite orders at least nineteen satisfying
its tame assumptions. A full evaluation-image equality with the residue
hyperplane would be a useful additional statement; the current degree proof
is complete through annihilation and explicit point interpolation.

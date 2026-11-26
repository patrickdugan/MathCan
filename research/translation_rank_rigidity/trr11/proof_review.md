# TRR-11 proof review

## Statement and representation

`tame_general_polynomialDecoder_degree_iff` assumes `[W.IsElliptic]` for an
arbitrary `WeierstrassCurve.Affine K`. Its statement has no short-normal-form
typeclass. The other hypotheses are finite odd marked order `N >= 19` and
nonzero images of `2`, `3`, and `N` in the coefficient field.

The decoder remains an actual `MvPolynomial (Fin 4) K`. `BlockDegreeLE`
requires `e 0 + e 1 <= d` and `e 2 + e 3 <= d` at every exponent in its
support. `PolynomialDecoderOn` evaluates on nonidentity subgroup inputs and
uses `assignedX u` at their sum. An inverse pair therefore tests the assigned
value. The formal identity point is outside the input coordinate domain.

## Coordinate and group transport

`shearModel W r s t` is the actual action of `VariableChange.mk 1 r s t`
on `W`. Its finite points map back to `W` by
`(x,y) -> (x+r,y+s*x+t)`. `shear_equation_iff` proves the substituted
equation algebraically with arbitrary generalized Weierstrass coefficients.

The inverse-pair criterion is proved from the generalized negation formula.
For addition, the slope on `W` at the image points equals the slope on
`shearModel W r s t` plus `s`. The secant proof uses distinct x-coordinates.
When they coincide outside the inverse case, the curve equations identify
the y-coordinates and justify the tangent calculation. Every denominator
cancelled in this proof has a nonzero witness.

`shearPointTo` and `shearPointFrom` act on actual Mathlib points. The finite
constructors receive proved curve equations; ellipticity supplies
nonsingularity. Their inverse proofs establish a bijection. The addition
proof deals with the identity and inverse cases separately before using
the coordinate formulas. `shearPointEquiv` packages an actual additive
equivalence, allowing Mathlib's order theorem to preserve `addOrderOf`.

The normal-form interface proves `W.toShortNF.u=1` and equality of its model
with the specified shear. Existing Mathlib instances give the short-form
and ellipticity properties used in the final theorem.

## Actual polynomials and the assigned value

`affineBlockPullback` expands each supported monomial of the given
four-variable polynomial into bivariate affine powers, then tensors the
two blocks. The source proves both its exact evaluation formula and the
ordinary degree bound. No invertibility assumption is needed for this
one-way degree preservation. `affineBlockOutput` applies an affine scalar
correction while preserving the same bound, including `d=0`.

For an additive point equivalence with x-coordinate shift `r`, the key
identity is

\[
\operatorname{assignedX}_{u+r}(e(P))
=\operatorname{assignedX}_u(P)+r.
\]

The proof includes `P=O`. This is required when the decoder inputs are
inverse points. Carrying only the finite-coordinate identity would leave
those entries unchecked.

`cyclicPointTransport` maps actual cyclic subgroup elements through integer
multiplication. The decoder proof uses the coordinate identities only at
nonidentity inputs, while the assigned-value identity applies at every
possible output.

The inverse affine map has parameters `(-r,-s,s*r-t)`. Applying the same
polynomial construction in each direction proves that existence with any
fixed block bound `d` is equivalent between the two coordinate models,
with the corresponding identity assignment.

## Final composition

The general theorem installs invertibility of `2` and `3` from their
nonzero field hypotheses. It forms the explicit short shear model and its
proved additive equivalence back to `W`. The marked point is pulled back
along that equivalence, preserving finite order, oddness and all numeric
order hypotheses.

The normalized assigned value is translated by the inverse x-shift. The
decoder-transport iff and TRR-10's exact short-model theorem then compose
directly. The new lower-bound and minimum-attainment corollaries are
applications of this iff.

The complete statement applies over arbitrary fields satisfying its
hypotheses. Passing to a finite extension introduces no additional proof
condition.

## Verification boundary

The audit retains every earlier source contract and adds 37 principal
reports, for 217 reports across 32 modules. Every source is compiled
directly after the complete aggregate build. Its report must match the
explicit declaration list and have transitive dependencies within
`propext`, `Classical.choice`, `Quot.sound`.

The mathematical controls must fail inside the deliberately altered
theorem. The new controls change the coordinate-translation sign and
remove the assigned-value shift. The earlier factor, threshold and sign
controls remain in the audit.

Independent finite arithmetic checks the full generalized equation grid
over F5 and F7 and the stated larger-field families. Its point additions
use direct generalized formulas. The retained decoder coefficients are
evaluated independently and transported back coefficient for coefficient.

The remaining formal work concerns lower bounds in characteristics
dividing the marked order and the small-order certificate interfaces.
Neither is used as an unstated premise of the theorem checked here.

# TRR-11: exact interpolation degree on generalized Weierstrass models

TRR-11 removes the short-form hypothesis from the checked tame interpolation
theorem. Lean proves the actual point-group equivalence, transports the
coordinate polynomial in both directions, and accounts for the assigned
identity value.

## Checked theorem

Let `K` be a field, and let

\[
E:y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6
\]

be smooth. Take a point `T` of finite odd order `N >= 19`. Assume the images
of `2`, `3`, and `N` are nonzero in `K`. Put `G=<T>` and `S=G\{O}`. Define
`f_u(O)=u`, and `f_u(P)=x(P)` on nonidentity points.

For every `u` in `K` and natural number `d`,

\[
\boxed{
\begin{aligned}
&\exists\mathcal D\in K[X_1,Y_1,X_2,Y_2],\qquad
  \deg_{(X_1,Y_1)}\mathcal D\le d,\quad
  \deg_{(X_2,Y_2)}\mathcal D\le d,\\
&\mathcal D(x(P),y(P),x(Q),y(Q))=f_u(P+Q)
  \quad\text{for every }P,Q\in S
\end{aligned}
\quad\Longleftrightarrow\quad d\ge\left\lceil\frac N3\right\rceil .
}
\]

The degree in each pair is ordinary total degree. The inputs range over the
nonidentity subgroup points, while their sum can be the identity.

The endpoint is
[`TRR08Geometry.tame_general_polynomialDecoder_degree_iff`](../../../experiments/trr08_geometry/TRR08Geometry/GeneralDecoder.lean).
It uses the actual Mathlib curve and point group, and an actual
`MvPolynomial (Fin 4) K`. Every generalized Weierstrass coefficient is
allowed subject to smoothness. The field can be infinite or a finite
extension, and the marked order can be composite.

## Coordinate change and assigned value

Write the usual invariants as

\[
b_2=a_1^2+4a_2,\quad b_4=a_1a_3+2a_4,\quad b_6=a_3^2+4a_6,
\]
\[
c_4=b_2^2-24b_4,\qquad
c_6=-b_2^3+36b_2b_4-216b_6.
\]

Completing the square and translating the x-coordinate gives

\[
F(x_g,y_g)=(x_g+r,\;y_g+s x_g+t),\qquad
r=\frac{b_2}{12},\quad s=\frac{a_1}{2},\quad t=\frac{a_3}{2}.
\]

Its short model is

\[
y_s^2=x_s^3+Ax_s+B,\qquad A=-c_4/48,\quad B=-c_6/864.
\]

The inverse map is

\[
F^{-1}(x_s,y_s)=(x_s-r,\;y_s-sx_s+sr-t).
\]

At the identity, `F(O)=O`. The assigned scalar must therefore move with the
x-coordinate:

\[
u_s=u_g+r.
\]

Given a short-model decoder `D_s` for `u_s`, the generalized-model decoder is

\[
D_g(X_1,Y_1,X_2,Y_2)=
D_s(X_1+r,Y_1+sX_1+t,X_2+r,Y_2+sX_2+t)-r.
\]

Affine substitution preserves the total degree in each pair. Applying the
inverse substitution proves the converse, so the same bound is attainable
in both models for the corresponding assigned values.

The Lean point map is oriented from the changed model back to the original.
For normalization its shear parameters are `(-r,-s,sr-t)`. The source proves
that Mathlib's `toShortNF` has unit scale one, then identifies it with that
actual shear model. The generic transport theorem states both directions
for any supplied additive point equivalence with the proved coordinate
formulas.

## What is proved about the point group

`GeneralCoordinates` proves the equation after substitution and the
transformation of the inverse point. The addition formulas are checked
with the translated slope. Its secant calculation uses the nonzero
x-difference; the tangent case proves and cancels the vertical derivative
denominator.

`ShortModelTransport` constructs maps between the actual point types from
those equations and smoothness. It proves that the maps are inverse and
respect addition, including identity inputs and inverse pairs. Their
additive equivalence preserves marked order.

`DecoderTransport` carries cyclic subgroup membership through integer
multiplication. Its assigned-value identity holds at every point, including
the identity. This allows `GeneralDecoder` to apply the complete TRR-10
theorem on the normalized model and return the exact statement above.

## Audit

The combined audit checks **217 principal theorem reports** across 32 source
modules, adding **37 reports** in five modules. Every reported transitive
dependency belongs to `propext`, `Classical.choice`, or `Quot.sound`.

| New module | Contribution | Reports |
|---|---|---:|
| `AffinePolynomial` | Actual affine substitution and ordinary block degree | 12 |
| `GeneralCoordinates` | Generalized equations, slopes and coordinate addition | 6 |
| `ShortModelTransport` | Actual additive equivalence and short-model normalization | 9 |
| `DecoderTransport` | Cyclic decoder equivalence with the assigned-value shift | 7 |
| `GeneralDecoder` | General-model exact degree, lower bound and construction | 3 |
| **New total** | | **37** |

The verifier retains the frozen TRR-10 declaration contract, checks the
installed Lean and Mathlib revisions, and compiles each audited source
directly. The receipt records every source hash and all inherited verifier
hashes. See [`formalization_receipt.json`](formalization_receipt.json) and
[`proof_review.md`](proof_review.md).

Five mathematical mutations must fail within the changed theorem. The new
controls reverse the sign of an input x-translation and omit the shift of
the assigned identity value. The inherited controls cover the residue
factor, the weight threshold and the residue-row sign.

## Exact finite controls

The checker independently enumerates all five-coefficient equations over
`F5` and `F7`, checks their discriminants, and compares the complete smooth
set with the coordinate-change parameterization. Over `F11`, `F13`, `F17`
and `F19`, it tests every smooth short model under six explicitly listed
affine changes.

| Quantity | Checked |
|---|---:|
| Five-coefficient tuples over F5 and F7 | 19,932 |
| All smooth generalized models over F5 and F7 | 16,906 |
| Selected generalized models over the larger fields | 5,280 |
| **Generalized models total** | **22,186** |
| Direct generalized group additions | 2,836,656 |
| Exact point orders | 221,688 |
| Actual residue covariance checks | 114,418 |
| Ordinary evaluation ranks | 71,807 |
| Explicit generalized decoder polynomials | 106 |
| Target entries evaluated from collected decoder coefficients | 17,432 |

The additions use the generalized secant and tangent formulas independently
of the short-model table. The decoder checks expand the affine substitution
into four-variable coefficient dictionaries. Applying the inverse
substitution recovers each short decoder coefficient for coefficient.

Every witness includes its full generalized curve equation, marked point,
assigned value and polynomial coefficients in
[`generalized_decoder_witnesses.json`](generalized_decoder_witnesses.json).
The receipt at [`coordinate_change_receipt.json`](coordinate_change_receipt.json)
specifies the coverage and hashes. Fixtures use one subgroup for each
encountered `(p,N)`, with both assigned values `0` and `1`.

The arithmetic controls reject a wrong normalization sign and an omitted
identity-value shift. A further control adds a multiple of the curve
equation: all table values remain correct, but the polynomial exceeds the
degree bound and is rejected. Optimized Python execution is rejected before
the scan starts.

The finite sweep contains 2,023 subgroup instances whose order is divisible
by the characteristic. They test the coordinate identities and transported
upper construction. The universal lower theorem retains its tame-order
hypothesis.

## Remaining formal scope

The generalized-coordinate transfer is complete. The lower bound when the
characteristic divides the marked order still requires the function-field
and divisor argument. The small-order integral certificates also need their
Lean connection to the same interpolation statement.

The receipt therefore sets
`tame_general_model_interpolation_theorem_formalized=true` and
`generalized_coordinate_transfer_formalized=true`. Its broader legacy flag
`full_interpolation_theorem_formalized` remains false until the other cases
are integrated. The result concerns this affine coordinate polynomial
representation. General computation costs require a separate transfer
argument.

## Reproduce

Use the pinned Lean `v4.35.0` and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. From the public repository root:

```sh
python research/translation_rank_rigidity/trr08/test_verifier.py \
  --output /tmp/trr11-parser-controls.json
python research/translation_rank_rigidity/trr11/check_coordinate_change.py \
  --output /tmp/trr11-coordinates.json \
  --witness-output /tmp/trr11-decoders.json
python research/translation_rank_rigidity/trr11/verify_formalization.py \
  --output /tmp/trr11-formalization.json
```

The shared public workflow retains every earlier audit and adds the
generalized-coordinate checks. Its `trr11-generalized-interpolation`
artifact contains receipts, direct compiler logs, the checked revision and
the full decoder coefficient bundle.

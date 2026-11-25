# TRR-08 proof review

## Compiled theorem and its boundary

`TRR08Geometry.tame_coefficient_exclusion` proves a contradiction on an actual
Mathlib Weierstrass curve from the two displayed identities below. The proof
uses Mathlib's point group, the integer order of the marked point, its affine
coordinates, and the curve discriminant.

Let `K` be a field in which `2` and `3` are nonzero. Suppose that `W` is in
short Weierstrass form and satisfies Mathlib's ellipticity hypothesis. Write

\[
W:y^2=x^3+Ax+B,
\qquad N=\operatorname{addOrderOf}(T),
\qquad n=(N:K).
\]

Assume `19 ≤ N` and `n ≠ 0`. The theorem states that there cannot exist a
function `a : ℕ → K` and a constant `c : K` satisfying

\[
a(k)^2=n\bigl(x(kT)+c\bigr)
\quad\text{whenever }kT\ne O,
\]

together with

\[
a(2k)=2a(k)+n\frac{3x(kT)^2+A}{2y(kT)}
\quad\text{whenever }kT\ne O\text{ and }2kT\ne O.
\]

These are exactly the hypotheses named `hconstant` and `hcocycle`. In the
written interpolation proof, the local coefficients of `1/Φ(x)` provide
`a`, and the eigenvector condition supplies the first identity. Formalizing
that construction remains necessary before Lean proves the complete
interpolation exclusion from a proposed decoder.

The theorem permits any finite marked order at least nineteen satisfying
the stated identities. Prime order is used elsewhere in the intended
application. Since `addOrderOf` is zero for a point of infinite order,
the numerical order hypothesis enforces finite order. The scalar `n` is
the actual natural-number cast of this order into the field.

`MarkedPoints.lean` and `Obstruction.lean` compile under Lean 4.35.0 with
Mathlib v4.35.0. Their principal axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The final adapter compiled after the
root modules were exported through Lean's public module interface.

The completed verifier subsequently built both target graphs and checked
all 43 principal reports, with 37 new reports. The pinned dependency and
source hashes are recorded in the linked receipt.

The verification harness records source hashes, command results, and axiom
reports in [`formalization_receipt.json`](formalization_receipt.json).
This review records the direct module builds; the harness receipt supplies
the status of its aggregate run.

## Root count and the doubling calculation

[`TranslationInterpolationRootBound.lean`](../../../MathCan/TranslationInterpolationRootBound.lean)
defines finite polynomials as coefficient lists in increasing order.
Its general theorem is

```lean
coefficients_zero_of_distinct_roots
  (roots p : List K)
  (hdistinct : roots.Nodup)
  (hlen : p.length ≤ roots.length)
  (hzero : ∀ x, x ∈ roots → evaluate p x = 0) :
  ZeroCoefficients p
```

Synthetic division proves this statement. Removing a root decreases the
quotient's coefficient-list length by one; distinctness permits
cancellation of the factor `x-a` at every remaining root. Trailing zero
coefficients are allowed. The theorem therefore applies directly to the
nine-entry coefficient list of the obstruction, including characteristics
where its degree drops.

The polynomial checked by `obstruction_evaluation` is

\[
\begin{split}
K(X)={}&\left[4(6X+3c)(X^3+AX+B)
 +(n-1)(3X^2+A)^2\right]^2\\
&-64n(X+c)(3X^2+A)^2(X^3+AX+B).
\end{split}
\]

Its full expansion into nine coefficients is proved over an arbitrary
field. The subsequent root theorem derives coefficient vanishing from
distinct evaluations. It extracts the coefficients of degrees five
through eight and applies the previously compiled classification in
`TranslationInterpolationUniform.lean`.

`doubling_implies_obstruction` derives `K(x)=0` from the curve equation,
the cleared tangent equation, the doubling coordinate formula, and the
two local-coefficient identities at the point and its double. Every
equality used in this elimination appears in the theorem's hypotheses.
Its only cancellation assumption is `n ≠ 0`; the calculation remains
valid when the tangent slope is zero.

The theorem `doubling_data_force_singularity` assembles these results.
Given at least nine distinct field coordinates with the displayed
pointwise doubling data, it proves

\[
4A^3+27B^2=0.
\]

All eleven audited theorems in this module compiled successfully. Their
axiom reports contain only the ordinary logical axioms listed above;
`quotient_length` is axiom-free. The export-header change to
`TranslationInterpolationUniform.lean` preserves its statements and
proofs.

## Actual point geometry

[`MarkedPoints.lean`](../../../experiments/trr08_geometry/TRR08Geometry/MarkedPoints.lean)
proves the coordinate facts used by the adapter for the points

\[
T,2T,\ldots,9T.
\]

Each point is nonidentity. The order condition also excludes equality
between one of these points and the negative of another, since the sum
of their positive indices is at most eighteen. Mathlib's theorem that
equal affine x-coordinates identify a point or its negative then gives
nine distinct x-coordinates.

The tangent denominator is proved nonzero by the actual group law:
its vanishing would force the point's double to be the identity.
For the short model, the module obtains the curve equation and doubling
x-coordinate from Mathlib's point definitions. Ellipticity gives
`4*A^3+27*B^2 ≠ 0` through the short-model discriminant formula.

[`Obstruction.lean`](../../../experiments/trr08_geometry/TRR08Geometry/Obstruction.lean)
passes the list of those nine coordinates into
`doubling_data_force_singularity`. Its remaining point data come from
the proved geometry, while `hconstant` and `hcocycle` supply the local
coefficients. The resulting discriminant equality contradicts
ellipticity.

The short-model hypothesis is explicit. The existence and degree
preservation of the affine coordinate change from a generalized
Weierstrass model remain outside this adapter.

## Evaluation and the assigned identity value

[`TranslationInterpolationEvaluation.lean`](../../../MathCan/TranslationInterpolationEvaluation.lean)
constructs the finite linear algebra for the decoder criterion. The
evaluation set is represented as `Option (Fin n)`; `none` denotes a
chosen pivot in the evaluation set. The identity of the curve is absent
from that set in the intended application.

The functional `dot` is an explicit finite sum. A nonzero pivot residue
permits construction of the basis

\[
B_a=e_a-\frac{\lambda_a}{\lambda_0}e_0.
\]

The module proves that these vectors span exactly the functional's
kernel. For a symmetric matrix whose rows lie in this kernel, its
nonpivot submatrix gives the tensor coefficients, and the resulting
decoder reconstructs every entry. Evaluating at the nonpivot points
proves uniqueness of those canonical coefficients.

Assigning the identity value adds `u` times the negation permutation
matrix. The sign in the eigenvector condition follows from the proved
finite point-mass calculation and the stated oddness of the residues:

\[
M_u\lambda=0
\quad\Longleftrightarrow\quad
M_0\lambda=u\lambda.
\]

The final `evaluation_pole_decoder_iff` theorem requires the geometric
evaluation-image statement

```lean
himage : ∀ v, (∃ p, eval p = v) ↔ dot lam v = 0
```

and proves the rest of the finite decoder/eigenvector equivalence. The
type of features is abstract. For polynomial features, a separate
interpretation must identify the finite tensor with a polynomial in
the two coordinate blocks and establish the required degree bound.
This is the precise role of the polynomial-evaluation interface still
to be supplied.

## Matching characteristic and the affine ideal step

`PointIdeals.lean` uses Mathlib's actual coordinate ring, fraction field,
and injective map from nonsingular points to the affine ideal class
group. Its theorem `point_ideal_ne_single_generator` says that the ideal
of a finite nonsingular point cannot be generated by one nonzero
coordinate-ring element.

Its direct Lean build returned exit code zero. Both principal axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

This supports the written matching-characteristic argument. Completing
that formal proof still requires the differential-kernel statement for
the function field and the passage from a rational function with divisor
`[P]-[O]` to a generator of the corresponding affine ideal. The tame
adapter assumes `n ≠ 0` and makes no matching-characteristic conclusion.

## Remaining proof obligations

The next formal bridge should construct the local coefficients from
`w=1/Φ(x)` on the actual curve and prove their logarithmic-derivative
addition identity. The interpolation application then needs the residue
calculation converting `M₀λ=uλ` into the square identity, together with
the evaluation-image equality used by the finite tensor theorem.

The current compiled theorem closes the actual-point geometry,
doubling elimination, degree-eight root count, and discriminant
contradiction after those two coefficient identities have been supplied.
The written proof in
[`trr07/uniform_probe.md`](../trr07/uniform_probe.md) remains the source
for the global residue and divisor steps. Claims about the complete
interpolation theorem should retain that distinction in their proof
status.

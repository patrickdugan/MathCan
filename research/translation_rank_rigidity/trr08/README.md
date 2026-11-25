# TRR-08: formalizing the geometric obstruction

TRR-08 proves the degree-eight root argument and applies it to Mathlib's
actual smooth Weierstrass curves. It also constructs the finite decoder
behind the residue criterion. The global residue and function-field steps
remain explicit proof obligations.

The source uses Lean 4.35.0. The separate geometry project pins Mathlib
v4.35.0 at `56a005855ea17e0b0958f73ec801ae140b0a1679`; the root MathCan
package keeps its Init-only dependency boundary.

## The new curve theorem

Let

\[
E:y^2=x^3+Ax+B,\qquad N=\operatorname{ord}(T)\ge19,
\qquad n=(N:K)\ne0,
\]

where the curve is smooth and the images of two and three in the field are
nonzero. The theorem `TRR08Geometry.tame_coefficient_exclusion` proves that
a function `a : ℕ → K` and a constant `c` cannot satisfy both

\[
a(k)^2=n\bigl(x(kT)+c\bigr)
\]

at every nonidentity multiple and

\[
a(2k)=2a(k)+n\frac{3x(kT)^2+A}{2y(kT)}
\]

whenever `kT` and `2kT` are nonidentity points.

The proof takes `N` from the actual order of the marked point. It derives
nine distinct coordinates from `T,2T,…,9T`, establishes the nonzero tangent
denominators, and uses Mathlib's curve and doubling equations. The polynomial
calculation then forces `4*A^3+27*B^2=0`, contradicting ellipticity.

This statement permits composite marked orders as well. Prime order enters
the intended interpolation application elsewhere. Characteristic five is
included; matching characteristic is excluded by the explicit `n ≠ 0`
hypothesis of this theorem.

## What Lean checks

| Module | Audited principal declarations | Content |
|---|---:|---|
| `MathCan.TranslationInterpolationRootBound` | 11 | Synthetic division, the distinct-root bound, the complete obstruction expansion, and elimination from doubling data |
| `MathCan.TranslationInterpolationEvaluation` | 12 | Explicit residue-kernel basis, symmetric tensor reconstruction, assigned identity value and the eigenvector criterion |
| `TRR08Geometry.MarkedPoints` | 11 | Actual curve points, distinct coordinates, tangent denominators, short-form equations and discriminant |
| `TRR08Geometry.Obstruction` | 1 | The actual-curve contradiction stated above |
| `TRR08Geometry.PointIdeals` | 2 | The nonzero class of a nonidentity point and the impossibility of a single nonzero generator for its affine ideal |

The verifier checks these **37 new principal declarations** and rechecks
the six audited declarations from `TranslationInterpolationUniform`.
Some modules contain additional helper lemmas. The counts above refer to
the explicit axiom-report contract, rather than the total number of Lean
declarations.

The root-count proof operates on concrete finite coefficient lists. Nine
distinct roots force all nine obstruction coefficients to vanish, even
when a leading coefficient vanishes in a particular characteristic.
The subsequent discriminant contradiction uses the TRR-07 coefficient
classification, whose statements and proofs are unchanged.

For the finite decoder, `Option (Fin n)` labels the evaluation set. Its
`none` value is a chosen pivot point in that set. Given a nonzero residue
at the pivot, the explicit basis is

\[
B_a=e_a-\frac{\lambda_a}{\lambda_0}e_0.
\]

The proof reconstructs the symmetric target matrix as `BCBᵀ`, where `C`
is the nonpivot submatrix. The negation permutation and odd residue
vector yield

\[
M_u\lambda=0\quad\Longleftrightarrow\quad M_0\lambda=u\lambda.
\]

The final evaluation theorem takes the image equality
`image(eval) = ker(λ)` as a hypothesis, then constructs feature
representatives and the decoder coefficients.

## Verification

[`formalization_receipt.json`](formalization_receipt.json) records the
actual Lean version, pinned Mathlib revision, source hashes and transitive
axioms for every audited declaration. The permitted logical dependencies
are `propext`, `Classical.choice` and `Quot.sound`. One root-count helper
has no axiom dependencies. The verifier rejects missing or additional
reports, proof admissions and any transitive axiom outside that set.

[`audit_verifier.json`](audit_verifier.json) records sixteen Python controls
for that contract, including missing reports, altered axiom dependencies
and admission tokens hidden behind quoted comment markers. These controls
exercise the verifier separately from the Lean proof checks.

The receipt always carries
`full_interpolation_theorem_formalized: false` at this stage. A successful
kernel check applies to the theorem statements in the table, including
their displayed hypotheses. The source review is in
[`proof_review.md`](proof_review.md).

To reproduce from the repository root:

```sh
cd experiments/trr08_geometry
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms Mathlib.GroupTheory.OrderOfElement Mathlib.Tactic.LinearCombination Mathlib.Tactic.Ring Mathlib.Data.List.FinRange
cd ../..
python research/translation_rank_rigidity/trr08/verify_formalization.py --output artifacts/trr08/formalization_receipt.json
```

The script builds both projects and then compiles each audited source
again to obtain its axiom reports. Logs accompany the output receipt.
The TRR-08 workflow runs the same checks on public CI and uploads its
receipt and logs. Its dependencies are pinned in the experiment's Lake
manifest. A private mirror can supply `--core-root` and
`--geometry-root`; the Lean source files remain identical.

## Remaining E6 work

The next step is to construct `a(k)` from the local expansion of
`w=1/Φ(x)` on the actual curve. A formal logarithmic-derivative addition
identity would establish the doubling hypothesis. The residue calculation
must then turn the interpolation eigenvector condition into the square
identity.

[`NEXT_GEOMETRIC_LEMMA.md`](NEXT_GEOMETRIC_LEMMA.md) gives a concrete follow-up
task, including a finite formula for the coefficient and the exact
unproved theorem needed by the compiled adapter.

The evaluation module needs its geometric image theorem and an
interpretation of the tensor as a polynomial with the required degree
in each coordinate block. Generalized Weierstrass equations also need
the formal coordinate-change argument preserving those degree bounds.

When the characteristic equals the subgroup order, the written proof uses
the kernel of the function-field differential and the divisor of a p-th
root. `PointIdeals.lean` provides the affine ideal contradiction at the
end of that route. The differential theorem and the passage from a
global function divisor to that affine ideal remain to be formalized.
The small-order certificates also await integration into the final Lean
interpolation theorem.

The uniform written proof and the completed empirical suite remain in
[`trr07`](../trr07/README.md). These formal developments concern the
specified interpolation model. A broader computational conclusion
requires its own reduction to that model.

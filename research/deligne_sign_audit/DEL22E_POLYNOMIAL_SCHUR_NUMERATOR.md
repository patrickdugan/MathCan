# DEL-22E: polynomial Schur numerator and arbitrary-rank bordered-minor converse

## Dependency and verification

DEL-22D [PR #259](https://github.com/patrickdugan/MathCan/pull/259)
merged at \`78c99e2\`, proving the invertible-pivot rank-d
conormal interpolation criterion for actual DEL-16 original-equation
Jacobians at arbitrary extension-field points.

The pinned Lean 4.35/Mathlib 4.35
[DEL-22E workflow #45156848915](https://github.com/patrickdugan/MathCan/actions/runs/45156848915)
**passed** the complete Deligne04 umbrella (3,605 build jobs).
All 12 new printed theorem-axiom audits contain only
\`propext\`, \`Classical.choice\`, and \`Quot.sound\`; the independent
arithmetic regressions passed as well.

## Ring-level polynomial numerator

For any commutative ring R and any d×d matrix H with border
column b, border row c, and corner v, define

\[
D=\det\begin{pmatrix}H&b\\c&v\end{pmatrix},
\qquad
\Delta=\det(H),
\qquad
q=\Delta v-c\,\operatorname{adj}(H)b.
\]

Both D and q are elements of R, with no division and no assumed
regularity of Delta. The checked
\`det_borderedPivot_eq_numerator_of_unit\` proves

\[
\boxed{\quad \Delta\in R^\times\ \Longrightarrow\ D=q.\quad}
\]

The theorem is valid over nonreduced rings, so it can be applied
after localizing any actual scheme-coordinate ring at the
principal open Delta. It remains separate work to formalize that
localization and identify its algebraic comparison with the
original critical incidence ideal.

Two checked generic naturality theorems prove that **both**
the bordered determinant and its adjugate numerator commute
with any commutative-ring homomorphism. Thus evaluation,
parameter specialization, and field extension preserve these
specific expressions without radicalizing the original ideal.

## Literal DEL-16 polynomials

\`OriginalPolynomialSchur.lean\` constructs the pivot matrix,
column, section-gradient row and corner from formal partials
of the *actual* DEL-16 lifted product equations
\`Deligne16.copyEquation\` and the fixed-last-coefficient section
\`Deligne16.fixedSection\`.

The resulting
\`fixedPolynomialPivotMinor\` and
\`fixedPolynomialPivotNumerator\` are literal elements of
\`MvPolynomial (Deligne16.Coord k s) K\`.
The kernel proves exact evaluation of both at any extension-valued
geometric point, before imposing smoothness or rank assumptions.

On a true original rank-d stratum, with d original rows R and
d source columns C selecting a nonzero pivot H, the kernel proves

\[
\boxed{
\operatorname{criticalOnTangent}(u,a,c)
\iff
\begin{cases}
u\in U^k,\ s_{a,c}(u)=0,\\
D_{R,C,j}(u)=0\quad\text{for every source coordinate }j.
\end{cases}
}
\]

This is \`criticalOnTangent_iff_fixedPolynomialPivotMinors_zero\`.
It uses the DEL-22D kernel-verified identification of the selected
Jacobian rows with the full conormal space, and the new generic
determinant-zero/Schur interpolation equivalence.
It is valid for d=0 as well as positive ranks and arbitrary
extension fields. The complete original equation ideal, including
redundant and nonreduced relations, remains unchanged.

## Independent finite-field and symbolic regressions

\`tests/test_deligne22e_schur_numerator.py\` checks determinant
versus adjugate numerator on random and singular blocks over
GF(4) and GF(9), plus transport GF(4) to GF(16).
It also compares both expressions as **sparse integer polynomials**
built from the actual original parabola, node, double-line,
radical-line, redundant and product-parabola Jacobian fixtures.
Those sparse symbolic tests verify the unrestricted polynomial
identity on the finite fixture family, including characteristic-two
degeneracies.

## Outstanding scheme-level steps

1. Prove the **unrestricted** universal bordered-determinant
   identity as an equality in the original polynomial ring when
   Delta need not be invertible, or formalize the localization
   map and apply the already proved unit-pivot theorem there.
2. Reindex each bordered determinant explicitly as the matching
   \`Deligne22A.augmentedMinorPolynomial\` generator. The actual
   polynomial is constructed, and its geometric evaluation is
   proved; that explicit generator equality is a separate bridge.
3. On the localized constant-rank-d **scheme** chart, reduce the
   complete augmented-minor ideal using elementary row operations.
   The scheme hypothesis must force original higher minors to
   vanish in the localized coordinate ring, not only on geometric
   residue fields. This matters on nonreduced fibers.
4. Prove the Kähler presentation and its
   \`Fitt_{n-d-1}\` determinantal identification for the
   actual section quotient, where n is the number of source
   coordinates and d<n. Presentation independence and localization
   compatibility remain new formal obligations.
5. General rank/minor converse, L-valued universal parameters,
   global witness projection/elimination, and Katz weak Lefschetz
   remain separate dependencies in [#253](https://github.com/patrickdugan/MathCan/issues/253)
   and parent [#191](https://github.com/patrickdugan/MathCan/issues/191).

No properness, global Bertini polynomial, or weak Lefschetz statement
is inferred from these pointwise finite-dimensional chart theorems.

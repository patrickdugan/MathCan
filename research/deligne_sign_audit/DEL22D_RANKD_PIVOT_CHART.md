# DEL-22D: invertible rank-d pivot conormal chart

## Starting point

DEL-22C PR #258 merged at 8188b93 after 33/33 workflows passed.
The exact extended universal critical ideal equality under a K-valued
parameter evaluation is kernel verified.

## General chart

Given any field L, a finite family of rows r_t in L^ι indexed
by Fin d and an injective or arbitrary pivot-column selection
C:Fin d -> ι with det(H) != 0 for H_(t,b)=r_t(C_b),
define the unique interpolation coefficients

\[
\lambda_b(g)=\sum_{a=0}^{d-1} g(C_a)(H^{-1})_{a,b}.
\]

There is an exact equivalence

\[
g\in\operatorname{span}_L\{r_t\}
\quad\Longleftrightarrow\quad
\forall j\in\iota,\quad
g_j=\sum_t \lambda_t(g)\,r_{t,j}.
\]

This follows because the pivot coordinates of any row-span
representation satisfy \lambda H = g_C and H is invertible.
The converse is immediate from the displayed row-span expression.
The theorem includes d=0, where the 0x0 determinant is 1 and
the criterion reduces to g=0.

The module RankDPivotInterpolation.lean encodes this result using
Matrix.vecMul, Matrix.nonsing_inv_mul and
Submodule.mem_span_range_iff_exists_fun.

## Genuine relative criticality

Select rows of DEL-16's literal original polynomial Jacobian at an
arbitrary geometric extension-valued point u. Assuming the chosen
rows span Deligne21G.geometricConormalRelations f u and the pivot
determinant is nonzero, the Kähler differential annihilates
the true tangent space iff all the above residuals vanish, together
with the original on-scheme and on-section conditions.
The statement retains all redundant and nonreduced equations.

The source module now also derives the selected-row-span equality from
rank(A)=d and a nonzero selected d×d original Jacobian minor, via
`Matrix.linearIndependent_rows_of_det_ne_zero`,
`LinearIndependent.of_comp`, and equality of finite-dimensional subspace
ranks. Thus the final theorem
`criticalOnTangent_iff_rankd_pivot_of_rank` assumes the genuine
original Jacobian rank and nonzero pivot directly. A later global
result must still establish existence of such a nonzero minor when
rank(A)≥d+1, in order to prove

\[
\operatorname{rank}(A)\le d
\iff\text{all size-(d+1) minors vanish}.
\]

The *polynomial* pivot equations result after multiplying rational
residuals by det(H), and require an adjugate/block determinant identity.
The scheme-level localized ideal equality and Kähler Fitting
presentation remain subsequent tasks.

## Verification gates

Pinned Lean 4.35 / Mathlib 4.35 full Deligne04 kernel workflow,
printed axiom list with no sorryAx or ofReduceBool, and
GF(4)/GF(9) determinant/row-span/rank-drop tests.
**Verified at `94993c8`:** the pinned Lean 4.35/Mathlib 4.35
[DEL-22D run 45139582750](https://github.com/patrickdugan/MathCan/actions/runs/45139582750)
passed the full Deligne04 build (3,603 jobs), all five new
`#print axioms` checks using only `propext`, `Classical.choice`,
and `Quot.sound`, and the exact GF(4)/GF(9) regression suite.
Repository-wide PR checks remain a separate acceptance gate.

Refs DEL-22C PR #258, DEL-22B issue #253, DEL-16 #191.

# DEL-15: the relative bad locus on a genuinely embedded affine line

**Date:** 2026-11-22. **Repo:** patrickdugan/MathCan.
**Predecessors:** DEL-10 (#179), DEL-11 (#181), DEL-12 (#182), DEL-13 (#185), DEL-14 (#187), all merged.
**Geometric source:** [Hexagon 2611.00789v1, Lemma 8](https://hexagonmath.org/2611.00789v1). The source note identifies itself as AI-generated and awaits independent expert review.

## Why this bridge is needed

The exact Jacobian discriminant c-ab from DEL-11 through DEL-14 applies to an unconstrained hypersurface in ambient affine space. The original proof restricts a hyperplane's equation to an embedded U^k. Ambient smoothness does not survive arbitrary restrictions, even when the embedding is smooth.

Here we construct a true, elementary embedded variety: the graph U_d of y=x+d in A². Its graph is a closed affine line; the Lean file proves its polynomial pullback identity. This model makes the relative derivative and relative bad-parameter polynomial explicit. It is a proof-level stepping stone toward the Jacobian/Fitting incidence for the general U^k.

## Actual polynomial restriction

Let

    F(X,Y) = XY+aX+bY+c,     U_d: Y=X+d.

The actual univariate restricted polynomial, represented by Mathlib's Polynomial K, is

    G(X) = X²+(d+a+b)X+(bd+c).

The Lean theorem eval_graphSection_eq_conic_restriction identifies the evaluation of G with DEL-12's real MvPolynomial conic evaluated along the graph. The kernel theorem derivative_graphSection proves the genuine Mathlib formal derivative

    G'(X) = 2X+d+a+b.

Set A=d+a+b, B=bd+c. Then the relative bad-locus discriminant is

    Delta_rel = A²-4B.

The polynomial Bézout identity is valid over any commutative ring, including characteristic two:

    (G')² - 4G = C(Delta_rel).

Therefore Delta_rel belongs to the ideal J_rel=(G,G') in K[X]. Over any field, Delta_rel≠0 supplies an explicit inverse constant and implies J_rel=(1). In particular, at every zero of G over any extension field, its derivative is nonzero. These are algebraic statements; using the scheme-theoretic hypersurface Jacobian criterion gives the corresponding smoothness interpretation.

The converse properness and the smoothness equivalence for *arbitrary* embedded subvarieties remain separate formal tasks.

## A genuine polynomial bad-locus certificate

The new multivariate polynomial in the four affine parameters (a,b,c,d) is

    P(a,b,c,d) = (d+a+b)²-4(bd+c).

Lean constructs P as an actual MvPolynomial (Fin 4) K and proves its exact evaluation formula. Evaluation at (1,0,0,0) equals 1 over every field, so P is formally nonzero, including over F2.

The DEL-10 finite-field selection theorem then gives a parameter in D(P) intersected with any supplied Katz-good principal open D(L), assuming that L is nonzero and that the coordinatewise combined degree is strictly smaller than the field cardinality. The chosen section is certified pointwise regular. Katz-goodness remains an explicit premise.

## Tangency counterexample in every characteristic

For a=b=0,c=1,d=-2, the ambient hypersurface is

    XY+1=0,

whose actual Jacobian ideal is the unit ideal by DEL-14. On U_{-2}, the restricted equation is

    G(X)=(X-1)².

At X=1 both G and its genuine derivative vanish, including in characteristic two. At the ambient point (1,-1), ∂F/∂Y=1 is nonzero. Thus the ambient discriminant c-ab equals 1 while the relative discriminant Delta_rel equals 0. A Bertini certificate that only tests the ambient Jacobian misclassifies this example.

## Reproducibility and limitations

- **Lean:** experiments/deligne_mathlib/Deligne04/EmbeddedLineBadLocus.lean, imported through Deligne04.lean. The proof uses actual Polynomial.derivative, MvPolynomial, Ideal.span, and the preceding DEL modules. The CI prints each theorem's axioms.
- **Exact independent oracle:** tests/test_deligne15_embedded_line.py checks the restriction, tangential chain rule, Bézout identity, polynomial Euclidean gcd for (G,G'), and rational critical points over prime fields F2, F3, F5, F7, F11, F13, F17.
- **Frozen corpus:** research/deligne_sign_audit/del15_tasks.jsonl contains 96 deterministic cases, split among regular, critical, tangent, and wrong-ambient-discriminant mutants.
- **Proof scope:** The graph U_d here is an embedded affine line. The arbitrary embedded product U^k requires equations for its coordinate ring, the relative conormal/Jacobian rank or Fitting incidence, a proper-closure proof, effective degree bounds, and Katz's perverse-sheaf weak-Lefschetz good locus. This PR does not import those geometric assertions as hidden Lean axioms.

**Merge gate:** pinned Mathlib 4.35 kernel and axiom audit, all 96 exact cases, MathCan-wide checks, backward compatibility. Draft until green.

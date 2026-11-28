# DEL-12: actual multivariate polynomial derivatives and critical-point discriminant

**Date:** 22 November 2026. **Repository:** patrickdugan/MathCan.
**Source:** [Hexagon 2611.00789v1, Lemma 8](https://hexagonmath.org/2611.00789v1) and Mathlib v4.35, Algebra/MvPolynomial/PDeriv.lean, RingTheory/Smooth/Local.lean.

## Mathematical statement

For the affine hyperplane family \(F_{a,b,c}(X,Y)=XY+aX+bY+c\), DEL-11 formally established the geometric critical-point discriminant \(c-ab\) through bilinear algebra. DEL-12 upgrades that calculation by using Mathlib's genuine polynomial partial-derivative derivations.

The variable type is Bool, with false indexing X and true indexing Y. The multivariate polynomial is constructed from MvPolynomial.X and MvPolynomial.C. Its evaluations give the original conic equation, and its actual partial derivatives satisfy

\[
\operatorname{pderiv}_{X}(F_{a,b,c})=Y+a,\qquad
\operatorname{pderiv}_{Y}(F_{a,b,c})=X+b.
\]

The identities hold over any commutative ring, including characteristic two.

Over a field, a simultaneous zero of the polynomial and both genuine derivatives exists exactly when \(c=ab\). Consequently for \(c\ne ab\), every point on \(F=0\) has a nonzero partial derivative. That is the precise hypothesis required by the Jacobian criterion for smooth affine hypersurfaces.

## Lean implementation

The Mathlib 4.35 module ConicJacobian.lean proves:

- eval_conicPolynomial: the actual polynomial evaluation equals the original quadratic phase;
- pderiv_conic_x / pderiv_conic_y: formal polynomial derivative identities;
- eval_pderiv_conic_x / eval_pderiv_conic_y: partial derivatives at any point;
- actual_jacobian_critical_iff: actual polynomial critical points exist precisely at discriminant zero;
- actual_jacobian_regular_off_discriminant: the nonzero discriminant excludes simultaneous derivative vanishing at every solution.

The last two theorems bridge to DEL-08's existing exact conic singularity calculation. No semisimplicity, characteristic-zero assumption, or division by two enters.

## What is still geometric

The theorem above proves the polynomial-level Jacobian certificate. The Mathlib repository already contains a local-algebra Jacobian criterion in RingTheory/Smooth/Local.lean. To obtain a full scheme smoothness result in MathCan, a future proof must construct the quotient ring K[X,Y]/(F), establish a suitable finite presentation and regular/local criterion at all primes, and connect the polynomial partial derivatives to the Kaehler differential map.

The intended object in the original proof is an arbitrary smooth affine embedded variety \(U^k\) with prescribed bilinear coordinate. The conic model does not provide its tangent-incidence construction or Katz weak Lefschetz open. Such extensions remain DEL-13 targets.

## Independent exact finite-field oracle

The Python oracle del12_oracle.py represents the conic as a sparse polynomial coefficient map, then computes its derivatives by formal monomial differentiation. Its computation is independent of DEL-11's declared gradient functions.

The 80-case task corpus includes 32 symbolic derivative examples, 24 actual singular critical-point examples, eight reversed-gradient mutant controls, eight inseparable Frobenius-power examples in characteristic two, and eight ambient-tangent-restriction controls.

The inseparable examples are important: \(\partial(X^p+c)/\partial X=0\) in characteristic \(p\), although the polynomial is generally nonzero. The tangent restriction example shows again that ambient smoothness does not imply smoothness of a section after restricting to an arbitrary embedded subvariety.

A passing exact oracle is an independent finite witness. General mathematical claims rely on the pinned Mathlib kernel proofs.

## Acceptance

Require green DEL-12 Mathlib CI with all printed axioms excluding sorryAx and ofReduceBool, all finite-field exact cases, MathCan-wide regression and compatibility workflows. The source Hexagon exposition reports it is AI-authored and unverified by a human; the geometric prerequisites remain explicit.

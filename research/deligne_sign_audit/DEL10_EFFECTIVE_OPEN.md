# DEL-10: effective finite-field witnesses for common hyperplane good opens

**Date:** 2026-11-22.
**Source:** [Hexagon 2611.00789v1, Lemma 8](https://hexagonmath.org/2611.00789v1), [Katz, Appendix A.3–A.5, pp. 219–221](https://web.math.princeton.edu/~nmk/old/ACT.pdf).
**Prior work:** DEL-08 graph immersion and fixed-coefficient chart; DEL-09 quasi-finite Proj composite and finite-field parameter descent.

## Mathematical theorem

For a finite field F of cardinality Q, a nonzero multivariate polynomial P in F[x_1,...,x_n] whose individual degrees are strictly less than Q has a nonzero evaluation at some vector a in F^n:

\[
P\ne0,\quad \deg_{x_i} P<Q\ (\forall i)
\quad\Longrightarrow\quad
\exists a\in F^n,\ P(a)\ne0.
\]

This is a direct Mathlib consequence of the multivariate polynomial vanishing theorem in Combinatorics.Nullstellensatz.

If B,L,C are nonzero polynomials defining principal-open conditions for Bertini smoothness, Katz weak Lefschetz, and the fixed-coefficient hyperplane chart, a sufficient condition for a common rational point is

\[
\deg_{x_i} B + \deg_{x_i} L + \deg_{x_i} C < Q
\qquad\text{for each parameter index }i.
\]

Indeed, the coordinate polynomial ring over a field has no zero divisors, and every degree of BLC is bounded by the sum of the individual degrees. The nonzero evaluation of BLC gives one point in all three principal opens. The three-open statement is proved in the Lean source file EffectiveFiniteOpen.lean.

## Scope and the essential geometric premise

The theorem provides a point once suitable **nonzero defining polynomials** are given, with a coordinate-wise degree bound. MathCan has not yet produced those polynomials from the actual bad-hyperplane incidence scheme of U^k and the generic-base-change locus of Katz A.5.

The actual Bertini and Katz good sets are established only as dense Zariski opens by the source geometry. The step from such open subsets to explicit equations and computable degree bounds is a separate challenge.

This bound is sufficient, rather than necessary. It can be conservative.

## Finite extensions and adversarial examples

The nonzero formal polynomial \(X^q-X\) vanishes on every F_q-rational point. Its degree q meets, rather than falls below, the strict threshold. Over F_(q^2), the same polynomial has q^2-q nonzero evaluations and satisfies q<q^2. The exact corpus checks this for q=2, 3, 5.

Over F_2, the two nonzero principal opens D(X) and D(X-1) are disjoint on rational points. Their product has degree two, which equals the size of F_2, so the theorem's degree condition fails. Over F_4 their intersection acquires rational points.

Conversely, X^q+1 has degree q and is nonzero at X=0. The strict degree bound is sufficient and is not an exact characterization of rational-point existence.

## Implementations

- Lean: experiments/deligne_mathlib/Deligne04/EffectiveFiniteOpen.lean proves single-polynomial, two-open and three-open witnesses in arbitrary finite fields and dimensions.
- Exact checker: research/deligne_sign_audit/del10_oracle.py evaluates sparse formal multivariate polynomials over extension fields.
- Corpus and verifier: del10_tasks.jsonl and del10_verify_tasks.py contain 81 tasks with exact ground-truth labels and adversarial controls.
- Regressions: tests/test_deligne10_finite_open.py independently exercise the degree budget and finite-field edge cases.

The corpus has 32 good three-open examples over F3/F4/F5/F8/F9/F16/F25/F27, eight independent-coordinate F2 examples, nine Frobenius-vanishing mutations, six finite-extension repairs, ten high-degree nonzero examples, eight zero polynomials, and eight incompatible F2 principal-open pairs.

## Next mathematical target

DEL-11 should address the geometric bad-parameter locus in the projective dual space: prove it is a proper closed subset for the actual embedded smooth U^k, construct a polynomial whose nonvanishing principal open lies inside the good locus, and trace the coefficients to a finite field. The required proof invokes genuine Bertini and Katz generic base change. The present finite-field theorem is reusable once those premises are established.

The Hexagon exposition is AI-authored and explicitly reports no human verification at publication. DEL-10 formalizes a conditional algebraic lemma about good-open selection, not the full étale-cohomology theorem.

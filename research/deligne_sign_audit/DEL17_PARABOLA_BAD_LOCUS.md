# DEL-17: explicit degree-three bad-hyperplane polynomial on an actual embedded U²

**Date:** 2026-11-22. **Repository:** patrickdugan/MathCan.
**Prerequisites:** DEL-08 graph embedding, DEL-10 effective finite-field principal opens, DEL-12 actual partial derivatives, DEL-15 restricted Jacobians, and the DEL-16 embedded-product incidence program.

## Genuine geometry

Take the smooth affine parabola U={(x,y) | y=x²} ⊂ A². Its product V=U² is smooth, with coordinates x₀,y₀,x₁,y₁. The fixed path-bilinear regular coordinate B=x₀x₁ gives a graph embedding after the ordinary coordinate immersion.

A hyperplane whose coefficient on B is exactly 1 restricts to

    G(x₀,x₁) = α x₀² + x₀x₁ + β x₁² + p x₀ + q x₁ + c.

These are genuine polynomials in K[x₀,x₁]. The two actual derivatives are

    G₀=2α x₀ + x₁ + p,       G₁=x₀ + 2β x₁ + q.

This restricted equation is a two-factor instance of the original graph-coordinate construction. The ambient hypersurface and the restricted section have different Jacobians; DEL-15's tangent counterexample motivates working with G and its actual partials.

## Degree-three Bézout certificate

For any commutative ring K, set

    d=4αβ-1,
    E(α,β,p,q,c) = d*c - α*q² - β*p² + p*q.

Then the following **global identity of polynomials** holds over K:

    d*G - α*G₁² - β*G₀² + G₀*G₁ = E.

It requires no field inverses, and remains valid in characteristic two. Hence the constant polynomial C(E) belongs to the ideal (G,G₀,G₁) in K[x₀,x₁]. Consequently every parameter carrying a critical zero of G satisfies E=0 over every extension field.

Define E as a genuine parameter polynomial in K[α,β,p,q,c]. It has total degree at most three and is nonzero over every field, witnessed at (α,β,p,q,c)=(0,0,0,0,1), where E=-1. This directly constructs a nonempty Bertini-regular principal open D(E) on the **actual** embedded parabola product U².

## Exceptional fibers: closure is larger than projection

When d≠0, the simultaneous gradient equations have a unique solution. Substituting yields the criterion E=0 for a critical section. At d=0, E=0 remains necessary and may include parameters with no critical section: over odd Fp, take α=1, β=4⁻¹, p=q=0, c=1. The gradient equations have solutions, but G=1 along that critical line. The eliminant E vanishes nonetheless.

This distinction matters: an algebraic elimination ideal describes the closure of the projected critical incidence. Its zero locus need not equal the actual projected incidence at exceptional parameter fibers. DEL-16's general elimination statement is deliberately one-directional.

In characteristic two d=-1=1, so the gradient system is always uniquely solvable. The same universal identity still works, without dividing by 2.

## Exact finite-field size of the certified regular open

For every finite field K=F_Q, the polynomial E vanishes on exactly Q⁴ of the Q⁵ affine parameter points. Therefore

    #D(E)(F_Q)=Q⁴(Q-1).

Proof by elementary fibers: Fix (α,β) and put d=4αβ-1. When d≠0, each choice of (p,q) forces exactly one c for which E=0, hence Q² bad parameters. When d=0, which can only happen in odd characteristic, α and β are nonzero and 4αβ=1. Then E=-α(q-2βp)², whose zero condition is q=2βp. There are Q choices of p, one matching q, and Q arbitrary values of c, again Q² bad parameters. Summing over Q² possible (α,β) yields Q⁴ zeros.

The independent Python oracle exhaustively checks every parameter over prime fields F2, F3, F5, F7 and F11. It also checks the Bézout polynomial's *formal coefficients* in Z[x,y], rather than relying solely on finite-field evaluations. This exact density counts the guaranteed principal Bertini open D(E), while some exceptional parameters on E=0 also define smooth sections.

## Effective finite-field selection and remaining geometry

If a separate nonzero Katz-good principal polynomial L exists and for every parameter coordinate i,

    degreeOf_i(E) + degreeOf_i(L) < |Fq|,

then DEL-10 supplies a rational parameter in D(E)∩D(L). The existence of L, with the desired weak-Lefschetz property, remains a geometric/perverse-sheaf premise. For smaller fields the DEL-09 finite-extension route can be used when its hypotheses are met.

The uniform Bertini theorem for arbitrary U^k still requires a general conormal/Jacobian-Fitting ideal, a proper-closure proof, and effective degree bounds. This PR instead delivers an explicitly certified nonzero bad-locus polynomial for a genuine embedded product.

## Verification

Lean module: experiments/deligne_mathlib/Deligne04/ParabolaProductBadLocus.lean, using true Mathlib MvPolynomial.pderiv, the identity, a five-variable parameter polynomial, nonzeroness, and critical-parameter implication.

The independent standard-library Python oracle uses exact sparse polynomial derivative arithmetic and validates the global identity over F2, F3, F5, F7, F11, F13, F17. A 96-case frozen corpus covers critical examples, regular certificates, exceptional closure-only parameters, and one-step wrong-sign mutants. Checks distinguish algebraic polynomials from their finite-field evaluation functions.

**Acceptance:** pinned Mathlib 4.35 kernel, printed axiom audit without admitted proofs, independent exact tests, and MathCan-wide compatibility. Draft until green.

The source Hexagon manuscript identifies itself as AI-authored and awaits independent expert mathematical review.

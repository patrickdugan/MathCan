# DEL-16: actual embedded-product equations, tangent incidence, and elimination soundness

**Date:** 2026-11-22. **Repository:** patrickdugan/MathCan.
**Geometric target:** [DEL-16 issue #191](https://github.com/patrickdugan/MathCan/issues/191), following the verified [DEL-15 #189](https://github.com/patrickdugan/MathCan/pull/189).

## Polynomial model of the embedded U^k

Give an actual affine presentation of U inside A^s by a family of defining polynomials

    f_j(z_0,...,z_{s-1}) = 0,    0≤j<r.

For each product coordinate copy 0≤l<k, DEL-16 constructs the **actual Mathlib MvPolynomial** in ambient variables indexed by Fin k × Fin s:

    F_{l,j} = rename (i ↦ (l,i)) f_j.

The proof eval_copyEquation states precisely that evaluating this polynomial at a product point u returns the value of f_j on the l-th copy. The theorem onEmbeddedProduct_iff identifies simultaneous satisfaction of all the product equations with membership of every factor in the original affine zero locus.

The true product ideal is the span of these renamed equations in K[z_{l,i}]. This works for arbitrary finite presentations, arbitrary characteristic, and any k. If smoothness is required later, it must be proved or supplied as a property of U; a list of equations alone does not guarantee smoothness.

## Fixed-last-coordinate section

For a chosen regular polynomial B in the product coordinate ring, the hyperplane-section polynomial is

    H_{a,c} = B + ∑_{l,i} a_{l,i} z_{l,i} + c.

The coefficient of B is fixed at 1. In Hexagon Lemma 8, B is the bilinear path phase from adjacent product factors. DEL-08 supplies the graph-embedding route.

The Lean proof eval_fixedSection checks evaluation of the actual polynomial, rather than an assumed formula.

## Relative Lagrange incidence and tangent pairing

For each product defining equation F_t, define the true Jacobian entry

    J_{t,i}(u) = eval_u(pderiv_i F_t).

For the hyperplane section, let g_i(u)=eval_u(pderiv_i H). A Lagrange critical certificate is a point on the product and section, together with multipliers λ_t with

    g_i(u) = ∑_t λ_t J_{t,i}(u)   for all i.

A tangent vector v of the embedded product satisfies

    ∑_i J_{t,i}(u) v_i = 0   for every constraint t.

The kernel theorem weighted_jacobian_tangent_zero proves that a gradient in the constraint row span annihilates all tangent vectors. The application lagrange_critical_annihilates_product_tangent uses the genuine MvPolynomial partial derivatives and holds in every commutative ring. No division by 2 enters the argument.

A converse from tangent annihilation to existence of λ requires linear-algebra rank assumptions; its equivalence to a singular section invokes the smoothness/Jacobian criterion. For a smooth complete intersection, the constraint Jacobian must be full rank at the points considered.

## Elimination soundness

Let I be an ideal of K[parameters,witnesses]. Its elimination ideal is the comap under the genuine ring homomorphism embedding parameter variables:

    I_param = I.comap (rename Sum.inl).

The kernel theorem elimination_sound_at_joint_zero proves any joint zero of I yields a parameter at which **every polynomial in I_param vanishes**. This is the sound inclusion needed to extract an effective bad-locus certificate. It does not assert that I_param contains a nonzero polynomial.

The next stage will construct a joint ideal for the actual equations F_{l,j}, H, and Lagrange gradient equations. It will then seek nonzero members of the corresponding elimination ideal by geometric incidence dimension and elimination, with degree bounds. Katz's weak-Lefschetz open is a separate geometric construction.

## Independent adversarial oracle

The deterministic 96-case finite-field corpus evaluates a nontrivial embedded product:

    U = {(x,y) : y-x²=0},    V=U²,

with the prescribed path-coordinate B=x₀x₁ and section

    H=x₀x₁+aₓ₀x₀+aᵧ₀y₀+aₓ₁x₁+aᵧ₁y₁+c.

The tangent equations are vᵧ,j=2x_j vₓ,j, and normal covectors are (-2x_j,1). The 96 cases include critical parameters, regular points, tangent-critical points with nonzero ambient gradient, and wrong-gradient-sign mutants. The oracle checks exact row-span identities across F2, F3, F5, F7, F11, F13, F17, as well as a separate elimination syzygy and the X^p-X polynomial-function trap.

## What still remains

1. Construct the joint **universal** incidence ideal with all parameters, embedded product coordinates, and multipliers in one polynomial ring.
2. Prove full relative critical equivalence under the correct rank/smoothness hypotheses, then relate it to the scheme-level Jacobian/Fitting criterion.
3. Show the closure of projected bad incidence has positive codimension, extract an explicitly nonzero defining polynomial, and bound its coordinate degrees.
4. Combine Bertini's polynomial with an independently constructed Katz perverse-sheaf good-open polynomial and apply DEL-10/DEL-09.

The Hexagon manuscript identifies itself as AI-generated and not yet independently reviewed by a mathematician. Formal claims in this PR remain limited to kernel-proved algebraic statements. Merge requires pinned Lean 4.35 kernel with axiom printout, 96-case oracle, and green MathCan compatibility workflows.

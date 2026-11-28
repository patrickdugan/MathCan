# DEL-20: coordinate cotangent spanning from an actual polynomial Jacobian

**Date:** 22 November 2026.
**Repository:** patrickdugan/MathCan.
**Predecessors:** merged DEL-16 polynomial embedded-product incidence and DEL-19 affine Bertini parameter surjectivity, PRs #193 and #206.
**General target:** DEL-16 issue #191.

## What the Lean proof constructs

Given a genuine finite polynomial presentation of an embedded affine U, let

    f_j ∈ K[z_0,...,z_{s-1}],   0≤j<r.

DEL-16 renames these actual Mathlib multivariate polynomials into every factor of the product U^k, with ambient indices Fin k × Fin s. DEL-20 takes a K-valued point u and constructs the subspace of first-order tangent vectors

    T_u = {v ∈ K^(ks) :
           ∀(l,j), Σ_i [eval_u(pderiv_i(copy_l f_j))] v_i=0}.

The derivatives are the real Mathlib MvPolynomial.pderiv functions on the lifted defining equations. The theorem mem_jacobianTangent_iff identifies this subspace with DEL-16's exact Jacobian-orthogonality predicate.

Its cotangent module is the vector-space dual T_u*. Each ambient coordinate induces a restricted covector dz_i(v)=v_i. The key Lean theorem coordinateCotangent_surjective proves the map from ambient coefficient vectors a to sum(a_i dz_i) in T_u* is surjective for EVERY subspace of a finite coordinate vector space, with no rank or smoothness assumptions.

The proof uses the pinned Mathlib 4.35 dual-restriction surjectivity theorem, extending any linear functional on the tangent subspace to the ambient vector space, and LinearMap.piRing to express that extension by coordinate coefficients. The companion theorem cotangent_eq_coordinate_sum gives the explicit formula

    ∀ φ∈T_u*, ∃ a, ∀ v∈T_u, φ(v)=Σ_i a_i v_i.

Instantiating with jacobianTangent f u yields polynomial_product_cotangent_span for the actual product equations. This removes the abstract cotangent-spanning hypothesis from DEL-19 when the tangent is modeled as the kernel of the true Jacobian of the chosen presentation.

The final theorem exists_fixed_phase_critical_on_jacobian_tangent chooses a and c for an arbitrary prescribed phase value B and cotangent differential dB:

    Σ_i a_i dz_i=-dB
    B(u)+Σ_i a_i z_i(u)+c=0.

This uses the freely variable scalar c to control the section value independently of its first derivative and holds over any field, including characteristic two.

## Mathematical scope

The algebraic tangent definition above is the Jacobian-kernel tangent for the *presentation ideal*. For the Zariski tangent space of Spec(K[z]/I), the defining equations must generate I as an ideal, and the standard scheme tangent/derivation equivalence must be connected to these Lean definitions. If only the pointwise zero set has been specified, the resulting scheme or tangent can differ.

This theorem proves coordinate covector spanning in finite-dimensional ambient coordinates without assuming the local tangent dimension is D. At singular points, that dimension may grow. The smooth-variety dimension assertion and the global incidence fiber-dimension theorem are separate geometric steps.

The remaining proof route is: identify the scheme tangent to U^k via the Kähler/cotangent-complex presentation, certify the smooth locus and constant geometric fiber dimensions, prove the projected relative critical incidence has proper Zariski closure, extract a nonzero polynomial with a degree bound, and combine its principal open with the independently constructed Katz weak-Lefschetz open. Mathlib 4.35 contains Algebra.Extension.toKaehler_surjective and local cotangent/Jacobian criterion interfaces that can support the next bridge.

## Independent exact verification

A 96-case JSONL regression file checks U² for U={(x,y): y=x²}, with the true constraint Jacobian

    [-2x0  1     0    0]
    [ 0   0   -2x1  1].

A tangent basis consists of (1,2x0,0,0) and (0,0,1,2x1). The coordinate restrictions span both cotangent directions over all tested prime fields, including F2, and the coefficient map onto any target covector has Q² solutions. The oracle also checks fixed-phase critical parameters, free-constant value control, incorrect omission of the x coordinates, and the singular-node example f=xy, where tangent dimension increases at the origin.

Corpus: research/deligne_sign_audit/del20_tasks.jsonl.
Exact verifier: tests/test_deligne20_cotangent_span.py.
Lean: experiments/deligne_mathlib/Deligne04/JacobianTangentCotangent.lean.

**Merge gate:** pinned Mathlib 4.35 kernel and printed axioms with no sorryAx, exact oracle, MathCan-wide and preceding DEL compatibility workflows. Keep the PR draft until green.

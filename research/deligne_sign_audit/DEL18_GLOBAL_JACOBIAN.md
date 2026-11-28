# DEL-18: actual global Jacobian unit ideal and effective finite-field selection

**Prepared:** 2026-11-22, MathCan.
**Base:** DEL-17 draft PR #196, whose actual parabola product U² has an explicit degree-three parameter polynomial and a pinned Lean kernel proof.
**Reference:** [DEL-18 issue #202](https://github.com/patrickdugan/MathCan/issues/202).

## Actual polynomial ideal

DEL-17's true section G in K[x,y] on the embedding U² is

    G = αx²+xy+βy²+px+qy+c.

DEL-18 constructs its actual polynomial Jacobian ideal

    J=(G, pderiv_false(G), pderiv_true(G)).

From the kernel-backed Bézout identity

    C(E) = (4αβ-1)G - α(G_y)² - β(G_x)² + G_x G_y

the new Lean theorem eliminant_mem_jacobian proves C(E) belongs to J. If E≠0 in a field, multiplying C(E) by C(E⁻¹) produces 1 in J. This proves J=top globally, with the exact polynomial ideal rather than a rational-point enumeration.

The proof remains valid in characteristic two, where partial derivatives of squared terms vanish and the mixed term supplies the regularity.

## Effective selection

The section is regular in the algebraic Jacobian sense at every geometric zero whenever E is nonzero, as certified by J=top. To choose a parameter rational over F_Q, the module uses DEL-10's combinatorial Nullstellensatz theorem with the actual DEL-17 five-variable polynomial P=E and a separately supplied nonzero Katz polynomial L.

The Lean statement assumes a coordinatewise degree budget

    degreeOf_i(P)+degreeOf_i(L) < Q

for all five coordinates. It then proves existence of t with P(t) and L(t) both nonzero and that the actual section at t has no simultaneous zero of G and its two true derivatives over F_Q.

The degree vector of P is (1,1,2,2,1) by inspection of its monomials. A separate pinned kernel proof of those exact degree bounds and the Q⁴(Q-1) rational count is a distinct milestone in issue #202; until then the combined degree inequalities remain explicit hypotheses.

## Exact independent tests

The standard-library oracle tests/test_deligne18_global_jacobian.py checks 1 as the normalized Bézout witness, absence of finite-field critical points when E≠0, characteristic-two families, and a synthetic Katz-principal-open example L=α for F3/F5/F7/F11. The test explicitly labels the mock principal open as synthetic: its algebraic nonvanishing has been verified, while weak Lefschetz is not inferred from a polynomial name.

The new code also imports DEL-17's frozen exceptional-parameter corpus to make sure E=0 is not silently upgraded to an equivalence with actual critical incidence.

## Scope

The global ideal criterion here concerns the actual embedded parabola product, not general U^k. For arbitrary U^k the relative conormal/Jacobian-Fitting incidence, its projected bad-locus properness, explicit degree bounds and Katz's perverse-sheaf good open remain separate geometric tasks tracked in [DEL-16 issue #191](https://github.com/patrickdugan/MathCan/issues/191).

**Acceptance:** DEL-17 merged and kernel green, DEL-18 pinned Mathlib kernel with axiom audit, independent exact oracle, MathCan-wide regressions. Keep the DEL-18 PR in draft until all checks pass.

# RHD-10C: a cyclotomic-unit obstruction to isolating the 29-adic character

**Setting.** E = Q(zeta_20); ell = 29; four Hensel factors modulo ell^2 = 841 as constructed by RHD-09. This note strengthens the finite arithmetic behind the globalization candidate. The corresponding HeightOneSpectrum and Hecke-character statements are mathematical deductions requiring a separate formalization.

## Exact computation

For each monic quadratic f_j(X) dividing Phi_20 modulo 841, put R_j = (Z/841)[alpha]/(f_j(alpha)). The residual extension has 29^2 elements. Every local unit u satisfies u^840 = 1 modulo 29. Define its principal-unit logarithm vector L_j(u) in F_29^2 by

    L_j(u) = (1 - u^840)/29 mod 29,

using the basis (1,alpha). This is well-defined because 840 = -1 mod 29, and it is an additive homomorphism from R_j^times to F_29^2. In particular L_j(1+29z) = z. The exact code uses repeated squaring in the quadratic ring and integer arithmetic throughout.

Two explicit global units are

    eps_1 = 1 - zeta_20,
    eps_3 = 1 - zeta_20^3.

Both are algebraic integers with absolute norm Phi_20(1) = 1. Their reductions yield:

| j | L_j(eps_1) | L_j(eps_3) | determinant mod 29 |
| --- | --- | --- | ---: |
| 0 | (13,14) | (0,28) | 16 |
| 1 | (17,23) | (20,3) | 26 |
| 2 | (14,23) | (7,3) | 26 |
| 3 | (14,14) | (2,28) | 16 |

Each determinant is nonzero. Consequently, the images of these two global units span the entire local first principal-unit layer at every prime above 29.

The norm-pullback Dirichlet exponents of eps_1 across j=0,1,2,3 are (27,2,2,27); for eps_3 they are (2,27,27,2). Each sum is zero modulo 29, consistent with the global norm 1.

## Conditional global consequence

For an order-29 finite-order idele-class character of E with trivial infinite components and ramification supported at only one such prime w, the restrictions at all other finite places are unramified and hence trivial on global units there. Triviality on the diagonally embedded global units forces the ramified local character to kill both eps_1 and eps_3.

Any continuous order-29 character of O_{E_w}^times factors through the first principal-unit layer: the residue-field unit group has prime-to-29 order, and the quotient of principal units by their 29th powers is F_29^2. A character's restriction therefore corresponds to an F_29-linear functional on that two-dimensional layer. Because the two unit log vectors above form a basis, a linear functional vanishing on both must vanish identically. Such a character is unramified at w.

This gives an **obstruction to nontrivial order-29 finite-order characters ramified at exactly one prime above 29**, subject to the stated finite-order, infinite-type, and ramification hypotheses. This does not exclude characters ramified at multiple primes, higher-order local characters, or different fields or conductors.

The RHD-09 character q composed with the norm from E to Q is compatible with the unit product formula precisely because its local exponents can cancel across all four primes.

## Upstream interface implications

At the pinned riemann-hypothesis source f150e026:

- SphOffU w0 S U asks for SatU at split places outside w0 and outside S.
- GenTy takes an S whose elements must lie away from ell.
- For the concrete norm-pullback order-29 character, three ramified primes besides w0 need to be excluded from a spherical Satake demand. These cannot be put into the ell-away S of GenTy when the exact same S is required.

Whether the source's downstream theorem uses the same S for both purposes needs a dedicated term-level dependency trace. Possible research directions are a two-set refinement, another automorphic family, or choosing a different field and prime. The single-prime-support shortcut for the *same order-29 finite character class* faces the cyclotomic-unit obstruction above.

## Verification and limits

Run:

~~~bash
python -m unittest tests.test_rhd10_unit_obstruction -v
python -m research.rh_proof_distillation.rhd10_unit_obstruction --output rhd10/unit_obstruction.json
~~~

The tests independently freeze all eight exact vectors, all four determinants, and the global norm product. They enumerate every nonzero linear functional in F_29^2 at each of the four local factors, proving that no such functional annihilates both unit images. The CLI emits an exact JSON receipt and SHA-256 sidecar.

These tests do not construct the places in HeightOneSpectrum, the actual p-adic unit groups, the idele-class character, or the original Lean TyEll eigenvector. Kernel proof work remains open.

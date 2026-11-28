# DEL-07: Katz A.5 to equivariant Gysin via Poincare duality

**Date:** 22 November 2026
**Source:** N. Katz, *Affine cohomological transforms, perversity, and monodromy*, JAMS 6 (1993), pp. 219–221, Appendix A.3–A.5. [Author PDF](https://web.math.princeton.edu/~nmk/old/ACT.pdf)
**Target:** [Hexagon 2611.00789v1](https://hexagonmath.org/2611.00789v1), Proposition 4, Theorem 7 and Lemma 8.
**MathCan:** pinned Lean/Mathlib 4.35 experiment.

## 1. Exact Katz inputs

Let f:Z→P^N be a separated, finite-type and quasi-finite morphism over an algebraically closed field of characteristic different from l. Let K be a perverse l-adic sheaf on Z. Katz A.3 proves a generic base change statement, A.4 gives the compact-support comparison, and A.5 obtains the generic hyperplane restriction

H^i(Z,K) → H^i(f^{-1}H,K),

which is an isomorphism for i<-1 and injective for i=-1.

For smooth Z of pure dimension D and a lisse sheaf G-dual, the shifted sheaf G-dual[D] is perverse. Thus a=D+i gives an isomorphism in ordinary degree a<D-1 and an injection at a=D-1.

**Boundary:** DEL-07 invokes this geometric theorem as a *source premise*. It does not formalize perverse sheaves, generic base change, or Katz A.3–A.5.

## 2. Duality shift and Tate normalization

Let X be smooth affine of pure dimension D>=1, and Y a smooth hyperplane section of dimension D-1. The transpose of the ordinary restriction in degree a, transported through the Poincare pairings, gives the compact Gysin map

G_j : H_c^j(Y,G)(-1) → H_c^{j+2}(X,G),  j = 2D-2-a.

For a=D-1 the source degree is D-1 and the target D+1. For a<D-1, j>D-1. These arithmetic claims are proved in KatzDegreeShift.lean.

On a smooth m-dimensional variety, Poincare duality transports compact Frobenius into the contragredient of *inverse* ordinary Frobenius times r^m, where r is the cardinality of the field of definition. The extra (-1) twist on the Y side contributes r, so r × r^(D-1)=r^D on both sides. This must be preserved when checking Frobenius compatibility.

## 3. Lean construction and proof boundary

KatzGysinDuality.lean defines a coordinate-free record with restriction r:HX→HY and perfect pairing equivalences PX:CX≃HX* and PY:CY≃HY*, all over C. It constructs the actual linear map

G = PX^(-1) ○ transpose(r) ○ PY.

Using Mathlib's genuine dual-map theorems, the module proves that restriction injectivity implies Gysin surjectivity and that restriction bijectivity implies Gysin bijectivity. With explicit Poincare/Frobenius compatibility assumptions it proves the transported Gysin map commutes with compact Frobenius. Its kernel is therefore an invariant submodule.

The pairings and their Frobenius equivariance remain *hypotheses*, because the existence and perfectness of actual l-adic cohomological duality are geometric facts. The construction proves their algebraic consequences and avoids equating a matrix toy model with actual etale cohomology.

## 4. Relation to the all-powers trace identity

For an equivariant short exact sequence

0 → K → CY → CX → 0,

the quotient action is Frobenius-compatible, so the trace on CY is the sum of the traces on K and CX for every positive Frobenius power. DEL-06 kernel-checked the adapted-block matrix statement, including arbitrary upper-right extensions. DEL-07 supplies the genuinely defined linear Gysin map whose exactness and equivariance justify that decomposition once actual geometric data are provided.

## 5. Independent exact-rational cases

The standard-library oracle del07_oracle.py constructs matrices G = inv(PX) transpose(R) PY and compact Frobenius B = inv(P) transpose(Ainv) P from *inverse ordinary* Frobenius Ainv. The compatibility square A_Y R = R A_X gives G B_Y = B_X G.

Exact matrix tests check kernel stability, trace differences over all tested powers, nonscalar perfect pairings, and nondiagonal Frobenius. The 64-case task corpus has 24 valid boundary injections with trace certificates, eight noninjective restrictions, eight broken equivariance squares, eight wrong untransposed dual actions, eight degenerate pairings, and eight degree-shift mutations.

The finite models supply verifier-grounded proof-repair examples. They neither establish Katz's theorem nor construct etale cohomology.

## 6. Remaining geometric obligations

1. Formalize actual l-adic sheaf cohomology, compact supports, Frobenius actions, and Poincare duality in the stated degrees.
2. Construct the projective quasi-finite embedding and the generic hyperplane with fixed bilinear coefficient. Apply Katz A.5 with its exact perverse hypothesis.
3. Identify the true Gysin maps with the transported transpose and check field-of-definition/Tate Frobenius normalization.
4. Connect Grothendieck trace formulas and Kunneth to the DEL-06 and DEL-05 spectral interface.
5. Obtain independent human mathematical review of the Hexagon exposition, which the authors identify as AI-generated and unchecked by a human.

Acceptance requires Mathlib kernel compilation with no sorryAx/ofReduceBool axioms, exact-rational mutation checks, and repository-wide regression tests.

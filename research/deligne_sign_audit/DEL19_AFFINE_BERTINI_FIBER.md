# DEL-19: fixed-coefficient Bertini incidence via cotangent spanning

**Date:** 22 November 2026. **Repo:** patrickdugan/MathCan.
**Target:** [DEL-16 issue #191](https://github.com/patrickdugan/MathCan/issues/191). This is a general pointwise linear-algebra bridge toward constructing a genuine nonzero Bertini bad-locus polynomial for the arbitrary embedded product U^k.

## The augmented affine parameter map

Let V=U^k be a smooth affine variety of dimension D, and z:V→A^M a closed immersion. For a geometric point v, the coordinate differentials dz_i(v) span T_v*V. Express this as an explicit assumption that every covector w is a linear combination of the dz_i.

For any prescribed regular phase B on V and a hyperplane with fixed coefficient 1 on B, write

    H_{a,c}(v)=B(v)+Σ_i a_i z_i(v)+c,
    dH_{a,c}(v)=dB(v)+Σ_i a_i dz_i(v).

The parameter map

    (a,c) ↦ (Σ_i a_i dz_i(v), Σ_i a_i z_i(v)+c)

is surjective onto T_v*V × K. Cotangent spanning lets us choose a for the desired differential. After choosing a, the constant c can be set uniquely to achieve any prescribed scalar section value. This is valid in all characteristics, including 2.

The Lean module AffineBertiniFiber.lean proves the augmented map's surjectivity as an actual Function.Surjective theorem over any field and finite coordinate indices, conditional on the stated cotangent-spanning property. A second theorem chooses (a,c) with H=0 and dH=0 for arbitrary fixed B,dB. It also proves the arithmetic codimension identity.

The geometric proof that the cotangent-spanning hypothesis holds for the actual U^k presentation is still required. The module does not assert an actual scheme dimension theorem from this pointwise linear-algebra statement.

## From linear algebra to Bertini

With dim(V)=D and parameter-space dimension M+1, the critical-incidence fiber over each smooth v is an affine linear solution space of codimension D+1. Thus its expected dimension is M-D. The total incidence dimension is M, one less than parameter space.

To finish the actual Bertini polynomial construction, formalize the relative incidence as a finite-type scheme, establish that the local fiber dimension is M-D everywhere, prove image-closure dimension at most M by algebraic geometry, then extract a nonzero polynomial from the ideal of the proper closed projected bad locus. Degree bounds are a separate effective elimination problem. The Katz perverse-sheaf weak Lefschetz open is independent geometric input.

## Exact finite-field U² witness and mutations

For U={(x,y): y=x²} and V=U², at a point (x0,x1) the four embedding-coordinate differentials are

    dz = [(1,0), (2x0,0), (0,1), (0,2x1)].

The augmented 3×5 matrix contains the 3×3 minor in columns (a0,a2,c):

    [1  0  0]
    [0  1  0]
    [x0 x1 1]

whose determinant is 1 over the integers. Every parameter fiber therefore contains exactly Q² elements over F_Q. An explicit parametrization takes freely chosen a1,a3 and solves uniquely for a0,a2,c. The exact oracle independently counts all q^5 parameter vectors for q=2,3,5 in selected fibers and checks the free-parameter formula across 96 deterministic cases in F2, F3, F5, F7, F11, F13, F17.

The corpus distinguishes normal surjectivity, fixed-phase critical sections, omission of the free constant, and loss of the embedding-coordinate differentials. The mutations prevent the algebraic conclusion from being silently extended to arbitrary coordinate maps or to fixed-constant parameter families.

## Scope and verification

Lean: experiments/deligne_mathlib/Deligne04/AffineBertiniFiber.lean.
Oracle: tests/test_deligne19_bertini_fiber.py.
Frozen corpus: research/deligne_sign_audit/del19_tasks.jsonl (96 examples).

The eventual theorem for the actual embedded U^k still requires the geometric cotangent-spanning and dimension/projection arguments. No general Bertini or Katz theorem is claimed in DEL-19. Merge requires pinned Mathlib 4.35 kernel proof, printed axiom audit, exact corpus and MathCan-wide checks.

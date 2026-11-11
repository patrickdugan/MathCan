# TOE-09: Lorentzian 2-form signature and the gauge-response spectrum

**Status (2026-11-11):** exact-rational 6×6 matrices, a conditional source-based gauge response, written derivations, 14 new regression methods and nine small Lean algebraic lemmas. This is a mathematical correction and extension of TOE-08C's *declared Euclidean Gram map*. It is not a full non-Abelian extension or a covariant solution of ΛGfE.

## Primary-source map and physical scope

Ginestra Bianconi, [*Gravity from entropy* (2025)](https://doi.org/10.1103/PhysRevD.111.066001), **Appendix A, Eq. (A1)** adds the gauge-field term `F_(mu nu) F_(rho sigma)` to the induced 2-form metric. **Appendix B, Eqs. (B18),(B30)** define the gauge-invariant bivector operator by raising a pair of 2-form indices using the metric on 2-forms. The Lorentzian metric has signature `(-,+,+,+)`; in an orthonormal basis of independent 2-forms `(01,02,03,23,31,12)` the induced 2-form metric has signature `(-,-,-,+,+,+)`. Bianconi, [*Λ-Gravity from Entropy* (2026)](https://arxiv.org/abs/2610.34496), Eqs. (5),(16), supplies `Θ=G_tilde g_tilde^-1` and the G-field as its inverse. The treatment of a single Abelian gauge field in the 2025 appendix is **source material**; the sum of color-indexed field-strength products over two isotropic SU(2) multiplets is a **declared MathCan hypothesis**. The 2026 paper's chosen scalar matter field has `M_(2)=0`.

The GfE 2-form operator generally includes curvature, matter, and its metric-variation terms. We are checking one particular input map to its spectrum, prior to making any tensor-propagation claim. No identification of the nonlinear SU(2) action or its covariant dressed stress tensor with Bianconi's field equations is assumed.

## 1. Covariant Gram form and Lorentzian raising

Consider two isotropic color triads with orthonormal-frame electric amplitudes `(E_1,E_2)` and magnetic amplitudes `(B_1,B_2)`. A color-summed source `Σ_{flavor,color} F_{μν}^{(flavor,color)} F_{ρσ}^{(flavor,color)}` has covariant flattened Gram matrix

\[
G_{F,2}=\begin{pmatrix}e I_3&cI_3\\cI_3&bI_3\end{pmatrix},\quad
 e=E_1^2+E_2^2,\quad b=B_1^2+B_2^2,\quad c=E_1B_1+E_2B_2.
\]

Raising its second 2-form index is matrix multiplication by `S=diag(-I_3,I_3)`, giving

\[
M_{F,2}=G_{F,2}S=\begin{pmatrix}-eI_3&cI_3\\-cI_3&bI_3\end{pmatrix}.\tag{1}
\]

A positive normalization factor from flattening conventions may be absorbed into `alpha`; it does not change the signature or the sign criterion. The sign of `c` depends on the orientation convention for magnetic basis vectors; its square and vanishing are invariant under reversing all magnetic axes. The electric sign is set by the Lorentzian metric.

Write `w=E_1 B_2-E_2 B_1`. Lagrange's identity gives

\[
eb-c^2=w^2,\quad
\det G_{F,2}=w^6,\qquad\boxed{\det M_{F,2}=-w^6}.\tag{2}
\]

Thus a full-rank Euclidean Gram response has an indefinite raised-index counterpart with three positive and three negative eigenvalues (when `w!=0`). The earlier TOE-08C Euclidean determinant remains correct for `G_(F,2)`; the physically relevant generalized eigenvalue problem uses the raised-index operator.

## 2. Positivity and the mixed-block discriminant

For an FLRW background define `A=H²+dot H`, `B=H²+K/a²`. In the five-sector isotropic curvature model used in TOE-04, `R_(2)` is diagonal with `2A` on the electric bivectors and `2B` on magnetic bivectors. Each of the three identical 2×2 blocks of the *declared* field-plus-curvature operator is

\[
\Theta_2=\begin{pmatrix}
 d_E&\alpha c\\-\alpha c&d_B
\end{pmatrix},\qquad
 d_E=1-\alpha e-2\beta A,\quad
 d_B=1+\alpha b-2\beta B.\tag{3}
\]

The characteristic polynomial is `λ²-(d_E+d_B)λ+d_E d_B+α² c²`, so

\[
\boxed{\mathscr D=(d_E-d_B)^2-4\alpha^2c^2
=[\alpha(e+b)+2\beta(A-B)]^2-4\alpha^2c^2}.\tag{4}
\]

A real diagonalizable positive spectrum requires `D>=0`, a positive trace and determinant, and absence of a nontrivial Jordan block at the repeated-root threshold. For `D>0`, those three inequalities suffice. When `D=0`, `c!=0` gives a defective 2×2 block. In the GfE logarithmic spectral interpretation, that boundary requires separate attention.

**Krein-space structure.** With `S_2=diag(-1,+1)` on each electric–magnetic pair, `Theta_2` satisfies

\[
\Theta_2^{\mathsf T}S_2=S_2\Theta_2.\tag{4a}
\]

It is self-adjoint for an *indefinite* inner product rather than the Euclidean one. This permits the real eigenvalues to collide at `D=0` and emerge as a complex-conjugate pair. At exact diagonal matching, the eigenvalues are `d_E ± i α c`; the repeated-root threshold with `c!=0` is a defective two-by-two matrix. The phenomenon is a finite-dimensional Krein collision, and no general claim about the quantum unitarity or stability of GfE follows from this algebra alone.

**TOE-09/T1 (diagonal matching has a stronger spectral gate).** If `d_E=d_B`, then `D=-4α² c²`. For `α>0`, a nonzero mixed response makes the eigenvalues nonreal. Hence diagonal E/B matching together with a real spectral requirement forces `c=0`.

This is separate from Pereira's TT principal-symbol condition. Even an admissible spectral operator would require a full coupled gravity–matter principal analysis.

## 3. An exact matched state loses real eigenvalues under a small perturbation

Choose `alpha=1/10`, `beta=1/50`, `H=1`, `dot H=-1/100`, spatial flatness, `E=(1/50,-1/50)`, and `B=(1/25,1/25)`. Initially `e+b=1/250`, `c=0`, and `d_E=d_B=3001/3125>0`. The 6×6 operator has six equal positive real eigenvalues.

Keep the geometry and magnetic field fixed and perturb `E_2` from `-1/50` to `-19/1000`. The mixed coefficient becomes `c=1/25000`, while the diagonal gap changes by only `39/10000000`. The **exact discriminant** becomes

\[
\boxed{\mathscr D=-\frac{4879}{100000000000000}<0}.\tag{5}
\]

This establishes a finite-perturbation example in the stated algebraic model. It is an input-space perturbation, not a solution of the Yang–Mills equations.

More generally, set `E(t)=(u,-u+t)`, `B(t)=(v,v)`, and choose the fixed curvature gap so the diagonals match at `t=0`. Then

\[
\mathscr D(t)=\alpha^2t^2[(2u-t)^2-4v^2].\tag{6}
\]

For `v>u>0`, sufficiently small nonzero `t` makes the discriminant negative. This gives an exact open interval of nonreal eigenvalues around the matched configuration along the declared perturbation direction.

**TOE-09/T2 (a dynamic necessary condition).** For differentiable `d_E-d_B=g(t)` and `c(t)`, if `g(0)=c(0)=0`, the leading discriminant is

\[
\mathscr D(t)=[g'(0)^2-4\alpha^2c'(0)^2]t^2+o(t^2).\tag{7}
\]

Thus `|g'(0)|<2α|c'(0)|` guarantees a negative discriminant sufficiently near the initial instant. The time derivatives must be computed from a self-consistent gravity–matter solution before applying the condition physically.

## 4. Verification and next proof gate

The exact-rational `lorentz_bivector.py` constructs all six-by-six entries, compares both determinants by independent Gaussian elimination, calculates the characteristic polynomial and checks a parameterized perturbation. `tests/test_toe09_lorentz.py` includes 625 exhaustive flavor tuples, 250 additional seeded rational cases, and a rational O(2) flavor-basis invariance check. The Lean module formalizes the integer sign/diagonal-match consequences, leaving the six-dimensional determinant and continuous eigenvalue perturbation as written mathematics checked by exact Python oracles.

To pursue actual GfE dynamics, extend the 2025 **Abelian** `F⊗F` metric in a manifestly gauge-invariant way, derive the complete `M_(2)` (including any Dirac–Kähler terms), and vary the 2026 action with the correct operator raising and G-field constraints. Then solve the coupled background and check the *full* tensor characteristic matrix, including off-diagonal E/B mixing. The SU(2) Yang–Mills and antisymmetric-tensor actions in TOE-08B/C remain trial matter actions with their own equations.

Run:

```shell
python -m unittest tests.test_toe09_lorentz -v
python -m research.toe.lorentz_bivector
python -m unittest discover -s tests -v
lake build MathCan
lake env lean MathCan/TOELorentzBivector.lean
```

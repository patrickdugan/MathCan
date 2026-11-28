# DEL-22A: original-scheme relative criticality, augmented rank and determinantal soundness

## Geometry and scope

Fix a field \(K\), a finite list of equations \(f\) for the original
closed immersion of \(U\subseteq\mathbb A_K^s\), and its literal DEL-16
lifted equations \(g_t\) for \(U^k\). The coordinate algebra is
\(A=K[z_i]/I\), where \(I=(g_t)_t\) includes the **original complete
ideal**, with nilpotent and redundant equations retained.

For a \(K\)-algebra field extension \(L\) and an on-scheme point
\(u:A\to L\), the actual DEL-21G conormal and Jacobian tangent are
\[
R_u=\operatorname{span}_L\{(\partial_i g_t(u))_i:t\},\qquad
T_u=\{v\in L^{ks}:\forall t,\ \sum_i\partial_i g_t(u)v_i=0\}.
\]
The quotient \(Q_u=L^{ks}/R_u\) is already kernel-identified with the
actual Kähler differential fiber \(L\otimes_A\Omega_{A/K}\) in DEL-21G.
DEL-21I/J/K established explicit tangent transport, tower composition
and the identity-field unit law for these actual modules.

Take a fixed-last-coefficient section as specified in DEL-16:
\[
s_{a,c}(z)=B(z)+\sum_i a_i z_i+c
\]
with \(a_i,c\in K\). DEL-22A forms \(ds_{a,c}(u)\) using the true
\(\mathrm{MvPolynomial.pderiv}\), followed by the geometric-point algebra
evaluation map. Theorems quantify over **arbitrary field extensions**
and use no radicalization or separability assumption.

## Kernel-verified criticality

The core equivalence is
\[
\boxed{  ds_{a,c}(u)|_{T_u}=0
  \iff ds_{a,c}(u)\in R_u
  \iff \operatorname{rank}\begin{bmatrix}J_u\\ds_{a,c}(u)\end{bmatrix}
      =\operatorname{rank}J_u .}
\]
The first equivalence is proved from Mathlib's genuine
`Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`, through the
finite-coordinate `LinearEquiv.piRing`. It compares the actual
DEL-21G conormal space and the original lifted-equation tangent.

The second equivalence is a whole-row-span theorem. The augmented
matrix indexes the section-gradient row with `none` and the original
Jacobian rows by `some t`. Lean proves that the original conormal
span is contained in the augmented span, and that equality of the
finite field ranks forces equality of these subspaces. For every
rank-\(d\) original Jacobian stratum, criticality is equivalently
the upper bound \(\operatorname{rank}J_{\mathrm{aug}}\le d\).

`sectionGradient_mem_conormal_iff_lagrange` also kernel-proves
the existence of **actual extension-field multipliers**
\(\lambda_t\in L\), satisfying
\[
\partial_i s(u)=\sum_t\lambda_t\partial_i g_t(u)
\quad\text{for all }i.
\]
The equivalence itself holds at singular and nonreduced points,
because it concerns the Jacobian tangent of the original scheme.
Interpreting it as ordinary smooth-divisor singularity still requires
the appropriate smoothness/rank hypotheses on \(U^k\).

## Actual polynomial minors

In `Deligne04.RelativeCriticalMinors`, the augmented Jacobian is
constructed **over the original polynomial ring** \(K[z]\) before
evaluation. The minor polynomial for each pair of index maps
\(\rho,\gamma:\operatorname{Fin}(d+1)\to\text{rows/columns}\) is
\[
D_{\rho,\gamma}
 = \det\bigl(J_{\mathrm{aug}}[\rho,\gamma]\bigr)\in K[z].
\]
Lean verifies \(\operatorname{aeval}_u(D_{\rho,\gamma})
=\det(J_{\mathrm{aug}}(u)[\rho,\gamma])\), using the ring-homomorphism
naturality of the determinant. A rank bound \(\le d\) forces the
size-\(d+1\) determinant to vanish, by `Matrix.rank_submatrix_le`
and `Matrix.rank_of_det_ne_zero`.

For each **fixed** choice of \(a,c\), the explicitly constructed
affine determinantal incidence ideal is
\[
J_{a,c,d}=I+(s_{a,c})+
      (D_{\rho,\gamma}:\rho,\gamma).
\]
The kernel-verified `fixedParameterCriticalIdeal_le_evalKer`
proves that, on the stratum where the original Jacobian has rank
exactly \(d\), every on-scheme critical point of \(s_{a,c}\)
annihilates this **entire** ideal over every extension field.
This is a necessary polynomial certificate for the geometric
critical incidence.

## Verification

Dedicated pinned Lean 4.35/Mathlib 4.35 actions:
- [Original-field rank and conormal theorem](https://github.com/patrickdugan/MathCan/actions/runs/45123333899)
- [Polynomial augmented minor ideal and soundness](https://github.com/patrickdugan/MathCan/actions/runs/45123801459)

All 13 printed theorem audits in the two modules contain exactly
`propext`, `Classical.choice`, and `Quot.sound`. No
`sorryAx` or `ofReduceBool` occurs in these proof dependencies.
The independent `tests/test_deligne22a_relative_critical.py`
checks the equivalence of conormal multipliers, annihilation of
finite-field tangent vectors, augmented rank and actual square
minors on parabola, node, nonreduced/radical line, redundant-equation
and product-parabola examples over characteristic two and odd
characteristic. It checks extension transport from
\(\mathbb F_4\) into \(\mathbb F_{16}\) and replays the frozen
DEL-21F/G/H/J arithmetic suites.

## Remaining geometric work

The determinant vanishing \(\Rightarrow\) rank-bound converse
is **not yet a Lean theorem** in this branch. A uniform
scheme-theoretic Fitting identification, smooth-stratum rank
hypotheses, universal parameter-ring coefficients \(a,c\),
elimination to the parameter space and proper-closure/dimension
arguments are separate DEL-16 milestones. Katz weak Lefschetz
continues to require its independent geometric input. In
particular, this local affine ideal does **not** assert that
its parameter projection is closed or that a nonzero universal
Bertini witness has been extracted.

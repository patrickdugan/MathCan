# DEL-21J: three-field Kähler cotangent and Jacobian tangent tower coherence

## Geometry retained

Fix the original DEL-16 lifted polynomials \(g_t\) with coordinate algebra
\(A=K[z_1,\ldots,z_{ks}]/I\), \(I=(g_t)_t\). All statements retain the
original ideal, including nilpotent structure and redundant equations.

At any extension-valued on-scheme point \(u:A\to L\), write
\[
R_u=\operatorname{span}_L\{(\partial_i g_t(u))_i:t\},\quad
Q_u=L^{ks}/R_u,\quad
T_u=\{v\in L^{ks}:\forall t,\sum_i\partial_i g_t(u)v_i=0\}.
\]

DEL-21G constructed \(Q_u\simeq_L L\otimes_A\Omega_{A/K}\) and
\(Q_u^\vee\simeq_L T_u\). DEL-21H transported the actual Kähler fiber and
dualized its extension equivalence. DEL-21I computed that dual-defined map
on \(1\otimes v\) and identified the DEL-21F/G maps at \(L=K\).

## Canonical three-field coherence

For compatible field algebra homomorphisms
\(\varphi:L\to_K M\), \(\psi:M\to_K N\), the actual \(N\)-linear
base-change equivalences satisfy the following identity of **entire maps**:
\[
\operatorname{BC}^{Q}_{L,N}\circ\alpha_Q
=\operatorname{BC}^{Q}_{M,N}\circ
  (1_N\otimes\operatorname{BC}^{Q}_{L,M}),
\qquad
\operatorname{BC}^{T}_{L,N}\circ\alpha_T
=\operatorname{BC}^{T}_{M,N}\circ
  (1_N\otimes\operatorname{BC}^{T}_{L,M}).
\]
The maps \(\alpha_Q,\alpha_T\) are Mathlib's genuine
\(`TensorProduct.AlgebraTensorModule.cancelBaseChange`\) in the direction
\(N\otimes_M(M\otimes_L V)\simeq_N N\otimes_L V\).

The Lean statements are
`Deligne21J.geometricCotangentTower_comp` and
`Deligne21J.geometricJacobianTangentTower_comp`.

The source proves these using `towerEquiv_comp_of_one_tmul`, a separate
tensor-extensionality theorem: unit-tensor agreement implies equality of
the two complete doubly base-changed linear equivalences. DEL-21I's
dualized tangent coordinate formula gives unit-tensor agreement for
\(T\), while DEL-21H's **full original-coordinate naturality square**
gives it for \(Q\). Quotient surjectivity handles every original
coordinate representative. The proof therefore compares the Kähler-defined
maps already constructed in DEL-21H, rather than defining new coordinate-only
substitutes.

## Concrete formulas and normalization

For every \(m\in M\), \(v\in T_u\), the genuine tangent equivalence
satisfies
\[
 \operatorname{BC}^{T}_{L,M}(m\otimes v)_i
      =m\,\varphi(v_i).
\]
For any coordinate representative \(w\in L^{ks}\), the actual conormal
quotient satisfies
\[
 \operatorname{BC}^{Q}_{L,M}(m\otimes[w])
      =m\,[\varphi(w_i)].
\]
Both are proved directly in Lean. Identity-field comparison lemmas
`geometricCotangentTower_id` and `geometricJacobianTangentTower_id`
compare the same DEL-21H equivalences with `TensorProduct.lid`.
The base-field \(L=K\) Kähler-map normalization remains the separate
kernel-verified DEL-21I theorem `geometricKahlerSelfEquiv`.

## Independent exact arithmetic regressions

`tests/test_deligne21j_three_field_towers.py` explicitly checks:

- \(\mathbb F_2\to\mathbb F_4\to\mathbb F_{16}\), using the
  DEL-21H embedded \(\mathbb F_4\) generator \(\alpha\mapsto\theta^5\).
  Two-stage and direct tensor coordinates agree; tangent-annihilator
  equations and original Jacobian relations survive both field maps.
- \(\mathbb F_3\to\mathbb F_9\xrightarrow{x\mapsto x^3}\mathbb F_9\),
  including the nontrivial field automorphism. The arithmetic tests
  composition on original polynomial derivatives and tangent vectors.
- Original nonreduced \(x^2\) versus radical \(x\) Jacobian rank
  contrast, along with nodal and product-parabola cases.

The pinned workflow compiles the complete `Deligne04` umbrella on Lean
4.35/Mathlib 4.35 and audits every new theorem using `#print axioms`.
The allowed axiom list is exactly `propext`, `Classical.choice`, and
`Quot.sound`. The generic unit-tensor theorem and both composition
squares already passed that audit in the dedicated
[initial full-composition run](https://github.com/patrickdugan/MathCan/actions/runs/45114962484);
the umbrella/normalization and additional oracle regressions are checked
on the PR's final head.

## Later geometric work

The next issue is an actual relative rank-drop locus for the original
module of Kähler differentials, with Fitting/Jacobian minors, consistent
scheme structure, and a separate elimination/properness proof before
projecting bad incidence onto Bertini parameter space. The local tower
coherence here does not assert those global geometric properties.

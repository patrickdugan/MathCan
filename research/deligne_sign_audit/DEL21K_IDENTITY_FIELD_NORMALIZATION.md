# DEL-21K: identity-field normalization of geometric Kähler and Jacobian tangent transport

## Result

Let \(K\) be a field, \(L/K\) any field extension, and
\(u:A\to L\) an on-scheme geometric point of the **original**
DEL-16 quotient \(A=K[z_1,\dots,z_{ks}]/I\). Retain every lifted
defining polynomial in \(I\), including nonreduced and redundant relations.

The geometric cotangent and Jacobian tangent modules are

\[
Q_u = L^{ks}/R_u, \qquad
R_u = \operatorname{span}_L\{(\partial_i g_t(u))_i : t\},\qquad
T_u = \{v : \forall t,\ \sum_i\partial_i g_t(u)v_i=0\}.
\]

DEL-21H constructed the actual Kähler-defined \(L\)-linear equivalence
\(E_\varphi: M\otimes_L Q_u\simeq_M Q_{\varphi u}\) for field maps
\(\varphi:L\to_K M\), and its **dual-defined** tangent equivalence
\(D_\varphi: M\otimes_L T_u\simeq_M T_{\varphi u}\).
DEL-21J kernel-verified their three-field composition.

DEL-21K proves the identity-arrow unit equations for both full maps.
Because Lean initially treats the destination at \(\mathrm{id}(u)\) as
a distinct dependent type, DEL-21K first supplies the canonical target
identifications

\[
\iota_Q:Q_{\mathrm{id}(u)}\simeq_L Q_u,\qquad
\iota_T:T_{\mathrm{id}(u)}\simeq_L T_u.
\]

The first is Mathlib's `Submodule.quotEquivOfEq` on the **original**
conormal relation subspace; the second is `LinearEquiv.ofEq` on the
literal Jacobian tangent subspaces. Both identities fix the original
coordinate representatives.

## Kernel statements

The Lean module `Deligne04.GeometricIdentityCoherence` proves

```
geometricCotangentTower_identity:
  geometricCotangentIdentityTransport f u hu
    = TensorProduct.lid L (geometricCotangentFiber f u)

geometricJacobianTangentTower_identity:
  geometricJacobianTangentIdentityTransport f u hu
    = TensorProduct.lid L (geometricJacobianTangent f u)
```

Each normalized transport is the **existing DEL-21H equivalence
composed with its canonical target identification**, preserving the
original Kähler-defined and dual tangent construction. On pure tensors,
the results are \(\iota_Q(E_{\mathrm{id}}(m\otimes[w]))=m[w]\)
and \(\iota_T(D_{\mathrm{id}}(m\otimes v))=mv\). The
`tensorLid_ext` lemma extends these to the **entire** tensor product
using the inverse of Mathlib's \(\operatorname{lid}\); it requires
neither a chosen basis nor additional finite-dimensionality assumptions.

Together with DEL-21J's composition identities, this supplies the
identity and composition coherences of the field-tower assignment of
actual original-ideal Kähler cotangent fibers and their Jacobian tangents.

## Verification

The dedicated pinned Lean 4.35/Mathlib 4.35 workflow
[45118547394](https://github.com/patrickdugan/MathCan/actions/runs/45118547394)
passed the new module and printed axiom audits for nine new declarations.
Every printed list contains only `propext`, `Classical.choice`, and
`Quot.sound`. The original DEL-21F/G/H/J finite-field regression suites
pass unchanged. The final PR run additionally builds the complete
`Deligne04` umbrella and all repository checks before merge.

This work concerns the local scheme geometry. The global Fitting/minor
rank-drop construction, elimination/properness and effective Bertini/Katz
steps remain separate proof obligations.

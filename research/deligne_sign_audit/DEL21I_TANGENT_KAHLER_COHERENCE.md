# DEL-21I: explicit tangent transport and base-field Kähler coherence

## Scope

This is the local-scheme continuation of DEL-21G and DEL-21H. All modules use the literal DEL-16 lifted defining polynomials for the quotient coordinate algebra
\(A=K[z_i]/I\), with the full original ideal \(I\), including nilpotent and redundant equations. None of the results replace \(I\) by a radical ideal.

## Field-extension tangent transport

For a field homomorphism \(\varphi:L\to_{K} M\), the DEL-21H isomorphism
\[
M\otimes_L T_u \simeq_M T_{\varphi(u)}
\]
was constructed by dualizing the genuine Kähler cotangent-fiber equivalence.

DEL-21I proves **the explicit formula for this very equivalence**, rather than defining an unrelated coordinatewise map:
\[
\operatorname{BC}_T(1\otimes v) = (\varphi(v_i))_i.
\]

The proof has two steps:

1. `geometricCotangentDualEquivTangent_coord` identifies each coordinate of DEL-21G's dual quotient with evaluation of the functional at the actual class \([e_i]\). It uses Mathlib's quotient annihilator and the finite coordinate dual equivalence.
2. `geometricJacobianTangentTowerEquiv_one_tmul` evaluates Mathlib's `IsBaseChange.toDualBaseChange` at a coordinate class and invokes DEL-21H's verified cotangent-basis transport formula. The resulting coordinates agree with \(\varphi(v_i)\).

This holds for any compatible extension-field algebra map, without imposing separability, reducedness, or an assumption that the Jacobian has full rank.

## Comparison at L=K

The file also proves:

- `onGeometricProduct_self`: the base-field original-ideal point satisfies the extension-valued point equations.
- `productGeometricPoint_self`: the DEL-21F and DEL-21G K-algebra evaluation maps are identical on the entire original quotient algebra.
- `geometricKahlerSelfEquiv_mk`: the two quotient-to-Kähler maps agree on each original coordinate representative, via DEL-21H's quotient identity.
- `geometricKahlerSelfEquiv`: the DEL-21F and DEL-21G Kähler linear equivalences agree on their entire source after the canonical conormal-quotient identification, proved from quotient surjectivity.

## Verification

The pinned Lean 4.35 / Mathlib 4.35 workflow passed on head `9935c04`, compiling `Deligne04.GeometricFiberCoherence`. The workflow logs list exactly these axioms for every new theorem: `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx` or `ofReduceBool`.

The dedicated workflow will also compile the complete `Deligne04` umbrella and replay the previously frozen DEL-21F/G/H arithmetic regressions, including the explicit finite-field towers \(\mathbb F_2\subset\mathbb F_4\subset\mathbb F_{16}\), \(\mathbb F_3\subset\mathbb F_9\), the characteristic-two nonreduced \(x^2\) versus \(x\) test, nodal examples and redundant original equations.

## Remaining optional extension

Composition coherence for arbitrary three-stage towers \(L\to M\to N\), after canonical tensor reassociation, remains an optional next theorem. The local Kähler and tangent naturality results here make no claim about global elimination, effective Bertini opens, incidence properness or Katz weak Lefschetz.

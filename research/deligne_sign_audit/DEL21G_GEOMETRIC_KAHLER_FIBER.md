# DEL-21G: geometric Kähler cotangent fibers over field extensions

**Branch:** `proof/deligne21g-geometric-fiber-20261122`  
**Parent:** [DEL-21 #212](https://github.com/patrickdugan/MathCan/issues/212)  
**Milestone:** [DEL-21G #235](https://github.com/patrickdugan/MathCan/issues/235)  
**PR:** [#236](https://github.com/patrickdugan/MathCan/pull/236)  
**Predecessor:** DEL-21F merged as [#230](https://github.com/patrickdugan/MathCan/pull/230).

## The original quotient scheme

Fix a field `K` and polynomial equations `f : Fin r → MvPolynomial (Fin s) K`.
DEL-16 defines their `k` lifted copies `g_t = copyEquation f t`,
with coordinate set `Coord k s` and equation set `EqCoord k r`.
The actual scheme coordinate ring is

```
A = K[z_(i,j)] / Ideal.span {g_t : t ∈ EqCoord k r}.
```

The ideal is preserved literally. In particular, `(x²)` is never
replaced by its radical `(x)`, nor is a redundant generator
discarded to construct the Kähler presentation.

## Arbitrary extension-field points

Let `L` be **any** field with `Algebra K L`.
For a point `u : Coord k s → L` with `aeval u g_t = 0` for each
original equation, `productGeometricPoint f u hu : A →ₐ[K] L`
is built from `Ideal.Quotient.liftₐ`. The theorem
`productGeometricPoint_mk` proves

```
productGeometricPoint f u hu ([P]) = MvPolynomial.aeval u P
```

for every polynomial `P` over the original `K`-coordinate ring.

This includes transcendental, inseparable, and non-algebraic field
extensions when the requisite `Algebra K L` instance exists;
no separability or flatness of the residue field as an A-module
is assumed.

## The L-linear conormal fiber

Define the original Jacobian row at an L-valued point by

```
geometricConormalRow f u t i :=
  MvPolynomial.aeval u (MvPolynomial.pderiv i (copyEquation f t))
```

and let `R_u` be their `L`-linear span in `Coord k s → L`.
The intended theorem of `geometricKahlerFiberEquiv` is

```
geometricCotangentFiber f u ≃ₗ[L] L ⊗[A] Ω[A⁄K]
```

with `geometricCotangentFiber f u = (Coord k s → L) ⧸ R_u`.
Equivalently,

```
L ⊗[A] Ω[A/K]  ≃_L  L^(ks)/span_L {grad(g_t)(u)}.
```

The proof uses the *actual* `Algebra.Presentation.differentials`
of `A=K[z]/I` from DEL-21E, and the right-exact tensor
base change of its genuine `Module.Presentation A Ω[A/K]`.
The coefficient theorem identifies every base-changed relation
with the original formal partial derivative, and the whole
relation-map equality identifies the image with `R_u`.
The first isomorphism theorem completes the quotient equivalence.

The dual result, `geometricKahlerFiberDualEquivTangent`, identifies

```
Dual_L (L ⊗[A] Ω[A/K]) ≃ₗ[L] geometricJacobianTangent f u
```

where tangent membership is characterized in Lean by the
actual original Jacobian-kernel equations

```
∀ t, ∑ i : Coord k s, geometricConormalRow f u t i * v i = 0.
```

## Compatibility and field homomorphisms

The `L=K` conormal row agrees with DEL-21D's evaluated
Jacobian row. Geometric points, their quotient-algebra maps,
and each original Jacobian-row coefficient commute with
arbitrary `K`-algebra homomorphisms `φ : L →ₐ[K] M`.
This covers composition along a tower of field extensions,
and prime-field Frobenius automorphisms.

Full naturality of the induced **tensor-quotient equivalence**
under further base change can be recorded as a separate
commutative-diagram theorem after DEL-21G's core results.
The point/row statements do not themselves assert that diagram.

## Regression

`tests/test_deligne21g_geometric_fiber.py` independently implements
the finite fields `GF(4) = GF(2)[α]/(α²+α+1)` and
`GF(9) = GF(3)[α]/(α²+1)`. Its cases include

- a parabola at a point with coordinates outside the base field
- the node `xy` at its singular origin and at an L-smooth point
- double line `x²=0` and radical mutant `x=0`
- redundant relations `(x²,x³)`
- two independent product-parabola factors
- pairing invariance modulo the exact row span
- prime-field Frobenius transport of the point and Jacobian.

The pinned Lean/Mathlib 4.35 proof must pass its explicit
`#print axioms` gate with only `propext`,
`Classical.choice`, and `Quot.sound`.

## Remaining global geometry

The relative singular-incidence scheme, elimination bounds
for bad-locus closure, effective finite-field parameter
selection, and Katz weak Lefschetz good-open arguments are
separate DEL geometric milestones. The cotangent-fiber result
supplies their correct local differential geometry over
geometric points.

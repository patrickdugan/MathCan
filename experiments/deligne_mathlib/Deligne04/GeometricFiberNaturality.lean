import Deligne04.GeometricKahlerFiber
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Tactic

/-!
# DEL-21H: naturality of the original-scheme Kähler fiber

Build on DEL-21G's *actual* Kähler differential quotient equivalence,
preserving the full original DEL-16 polynomial ideal.

Our first target is the field-tower associativity map
  M ⊗[L] (L ⊗[A] Ω[A/K]) ≃ₗ[M] M ⊗[A] Ω[A/K]
for the algebra maps A → L → M induced by a geometric point and
a K-algebra field homomorphism. Then we match the geometric conormal
quotient and show naturality on original coordinate generators.
-/

open TensorProduct Module

namespace Deligne21H

/-- The L→M homomorphism gives a compatible tower of algebra
structures over the genuine original quotient ring A=K[z]/I. -/
theorem geometricPoint_tower
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
    letI : Algebra L M := φ.toRingHom.toAlgebra
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) M :=
      (Deligne21G.productGeometricPoint f (fun i => φ (u i))
        (Deligne21G.onGeometricProduct_map f u hu φ)).toRingHom.toAlgebra
    IsScalarTower (Deligne21E.productCoordinateRing (k := k) f) L M := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
  letI : Algebra L M := φ.toRingHom.toAlgebra
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) M :=
    (Deligne21G.productGeometricPoint f (fun i => φ (u i))
      (Deligne21G.onGeometricProduct_map f u hu φ)).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change Deligne21G.productGeometricPoint f (fun i => φ (u i))
      (Deligne21G.onGeometricProduct_map f u hu φ) x =
    φ (Deligne21G.productGeometricPoint f u hu x)
  exact congrArg (fun ψ : _ →ₐ[K] M => ψ x)
    (Deligne21G.productGeometricPoint_map f u hu φ).symm

/-- The canonical associativity isomorphism on the *actual* Kähler
fiber along a field tower, with the full DEL-16 ideal retained. -/
noncomputable def geometricKahlerCancelBaseChange
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
    letI : Algebra L M := φ.toRingHom.toAlgebra
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) M :=
      (Deligne21G.productGeometricPoint f (fun i => φ (u i))
        (Deligne21G.onGeometricProduct_map f u hu φ)).toRingHom.toAlgebra
    M ⊗[L] (L ⊗[Deligne21E.productCoordinateRing (k := k) f]
      Ω[Deligne21E.productCoordinateRing (k := k) f⁄K]) ≃ₗ[M]
    M ⊗[Deligne21E.productCoordinateRing (k := k) f]
      Ω[Deligne21E.productCoordinateRing (k := k) f⁄K] := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
  letI : Algebra L M := φ.toRingHom.toAlgebra
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) M :=
    (Deligne21G.productGeometricPoint f (fun i => φ (u i))
      (Deligne21G.onGeometricProduct_map f u hu φ)).toRingHom.toAlgebra
  letI : IsScalarTower (Deligne21E.productCoordinateRing (k := k) f) L M :=
    geometricPoint_tower f u hu φ
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange
    (Deligne21E.productCoordinateRing (k := k) f) L M M
      Ω[Deligne21E.productCoordinateRing (k := k) f⁄K]

/-- The associator sends a pure field-tower Kähler differential
tensor to its single-step specialization in the original A-module. -/
theorem geometricKahlerCancelBaseChange_tmul
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M)
    (m : M) (l : L)
    (ω : Ω[Deligne21E.productCoordinateRing (k := k) f⁄K]) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
    letI : Algebra L M := φ.toRingHom.toAlgebra
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) M :=
      (Deligne21G.productGeometricPoint f (fun i => φ (u i))
        (Deligne21G.onGeometricProduct_map f u hu φ)).toRingHom.toAlgebra
    geometricKahlerCancelBaseChange f u hu φ
      (m ⊗ₜ[L] (l ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f] ω)) =
    (φ l * m) ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f] ω := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
  letI : Algebra L M := φ.toRingHom.toAlgebra
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) M :=
    (Deligne21G.productGeometricPoint f (fun i => φ (u i))
      (Deligne21G.onGeometricProduct_map f u hu φ)).toRingHom.toAlgebra
  letI : IsScalarTower (Deligne21E.productCoordinateRing (k := k) f) L M :=
    geometricPoint_tower f u hu φ
  change (l • m) ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f] ω =
    (φ l * m) ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f] ω
  rw [Algebra.smul_def]
  rfl

#print axioms geometricPoint_tower
#print axioms geometricKahlerCancelBaseChange_tmul

end Deligne21H

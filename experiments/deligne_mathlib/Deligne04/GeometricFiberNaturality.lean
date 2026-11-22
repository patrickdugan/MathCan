import Deligne04.GeometricKahlerFiber
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Dual.BaseChange
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
open scoped BigOperators

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

/-- The actual geometric Kähler-fiber equivalence acts on a class
of coordinates by the original differential-presentation surjection.
This records the representative-level construction of DEL-21G. -/
theorem geometricKahlerFiberEquiv_mk
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (v : Deligne16.Coord k s → L) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
    (Deligne21G.geometricKahlerFiberEquiv f u hu)
      (Submodule.Quotient.mk v) =
    ((Deligne21E.productKahlerPresentation (k := k) f).toSolution.π.baseChange L)
      ((Deligne21G.geometricCoordinateTensorEquiv
        (ι := Deligne16.Coord k s)
        (Deligne21G.productGeometricPoint f u hu)).symm v) := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
  rfl

/-- Over an arbitrary field tower, finite coordinate functions
base-change canonically via the usual coordinatewise map. -/
noncomputable def fieldTowerCoordinateEquiv
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {ι : Type*} [Fintype ι]
    (φ : L →ₐ[K] M) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    (M ⊗[L] (ι → L)) ≃ₗ[M] (ι → M) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  classical
  exact ((Pi.basisFun L ι).baseChange M).repr.trans
    (Finsupp.linearEquivFunOnFinite M M ι)

/-- A coordinate in the base-changed function module is the
field-homomorphic evaluation of its original scalar coefficient. -/
theorem fieldTowerCoordinateEquiv_one_tmul
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {ι : Type*} [Fintype ι]
    (φ : L →ₐ[K] M) (v : ι → L) (i : ι) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    fieldTowerCoordinateEquiv (ι := ι) φ (1 ⊗ₜ[L] v) i = φ (v i) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  classical
  simp only [fieldTowerCoordinateEquiv, LinearEquiv.trans_apply,
    Finsupp.linearEquivFunOnFinite_apply, Basis.baseChange_repr_tmul]
  change (v i) • (1 : M) = φ (v i)
  simp only [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
  rfl

/-- The original coordinate basis becomes the same coordinate
basis over the extension field. -/
theorem fieldTowerCoordinateEquiv_single
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : L →ₐ[K] M) (i : ι) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    fieldTowerCoordinateEquiv (ι := ι) φ
      (1 ⊗ₜ[L] (Pi.single i (1 : L))) = (Pi.single i (1 : M) : ι → M) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  classical
  ext j
  rw [fieldTowerCoordinateEquiv_one_tmul]
  by_cases hij : j = i
  · subst j
    simp
  · simp [Pi.single_apply, hij, Ne.symm hij]

/-- Actual original-ideal geometric cotangent quotients form a
canonical field-tower base-change equivalence, obtained by
transporting DEL-21G's genuine Kähler equivalence through the
Kähler tensor associator. The diagram commutes by construction;
a separate generator equation identifies the coordinate formula. -/
noncomputable def geometricCotangentTowerEquiv
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    M ⊗[L] Deligne21G.geometricCotangentFiber f u ≃ₗ[M]
      Deligne21G.geometricCotangentFiber f (fun i => φ (u i)) := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
  letI : Algebra L M := φ.toRingHom.toAlgebra
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) M :=
    (Deligne21G.productGeometricPoint f (fun i => φ (u i))
      (Deligne21G.onGeometricProduct_map f u hu φ)).toRingHom.toAlgebra
  letI : IsScalarTower (Deligne21E.productCoordinateRing (k := k) f) L M :=
    geometricPoint_tower f u hu φ
  exact ((Deligne21G.geometricKahlerFiberEquiv f u hu).baseChange L M _ _).trans
    ((geometricKahlerCancelBaseChange f u hu φ).trans
      (Deligne21G.geometricKahlerFiberEquiv f (fun i => φ (u i))
        (Deligne21G.onGeometricProduct_map f u hu φ)).symm)

#print axioms geometricKahlerFiberEquiv_mk
#print axioms fieldTowerCoordinateEquiv_one_tmul
#print axioms fieldTowerCoordinateEquiv_single
#print axioms geometricCotangentTowerEquiv
/-- The DEL-21G Kähler-fiber quotient map sends the class of a
coordinate basis vector to the true Kähler presentation's differential
of that original coordinate generator. -/
theorem geometricKahlerFiberEquiv_single
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (i : Deligne16.Coord k s) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
    (Deligne21G.geometricKahlerFiberEquiv f u hu)
        (Submodule.Quotient.mk (Pi.single i (1 : L))) =
    (1 : L) ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f]
      ((Deligne21E.productKahlerPresentation (k := k) f).toSolution.π)
        (Finsupp.single i (1 : Deligne21E.productCoordinateRing (k := k) f)) := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
  classical
  rw [geometricKahlerFiberEquiv_mk]
  let e := Deligne21G.geometricCoordinateTensorEquiv
    (ι := Deligne16.Coord k s) (Deligne21G.productGeometricPoint f u hu)
  have hi : e.symm (Pi.single i (1 : L)) =
      (1 : L) ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f]
        (Finsupp.single i (1 : Deligne21E.productCoordinateRing (k := k) f)) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (Deligne21G.geometricCoordinateTensorEquiv_single
      (ι := Deligne16.Coord k s)
      (Deligne21G.productGeometricPoint f u hu) i).symm
  change ((Deligne21E.productKahlerPresentation (k := k) f).toSolution.π.baseChange L)
      (e.symm (Pi.single i (1 : L))) = _
  rw [hi]
  exact LinearMap.baseChange_tmul
    (f := (Deligne21E.productKahlerPresentation (k := k) f).toSolution.π)
    (1 : L) (Finsupp.single i (1 : Deligne21E.productCoordinateRing (k := k) f))

/-- Generator-level agreement of the full Kähler-tower composite
with transport of the original cotangent-coordinate classes.
This determines the base-change square on every finite coordinate
generator, rather than merely declaring a composite equivalence. -/
theorem geometricCotangentTowerEquiv_single
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M)
    (i : Deligne16.Coord k s) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    geometricCotangentTowerEquiv f u hu φ
      ((1 : M) ⊗ₜ[L] (Submodule.Quotient.mk (Pi.single i (1 : L)))) =
    Submodule.Quotient.mk (Pi.single i (1 : M)) := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (Deligne21G.productGeometricPoint f u hu).toRingHom.toAlgebra
  letI : Algebra L M := φ.toRingHom.toAlgebra
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) M :=
    (Deligne21G.productGeometricPoint f (fun j => φ (u j))
      (Deligne21G.onGeometricProduct_map f u hu φ)).toRingHom.toAlgebra
  letI : IsScalarTower (Deligne21E.productCoordinateRing (k := k) f) L M :=
    geometricPoint_tower f u hu φ
  let eL := Deligne21G.geometricKahlerFiberEquiv f u hu
  let eM := Deligne21G.geometricKahlerFiberEquiv f
    (fun j => φ (u j)) (Deligne21G.onGeometricProduct_map f u hu φ)
  apply eM.injective
  simp only [geometricCotangentTowerEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.baseChange_tmul]
  rw [geometricKahlerFiberEquiv_single f u hu i]
  rw [geometricKahlerCancelBaseChange_tmul]
  rw [geometricKahlerFiberEquiv_single f (fun j => φ (u j))
    (Deligne21G.onGeometricProduct_map f u hu φ) i]
  simpa only [map_one, one_mul] using
    (eM.apply_symm_apply
      ((1 : M) ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f]
        ((Deligne21E.productKahlerPresentation (k := k) f).toSolution.π)
          (Finsupp.single i (1 : Deligne21E.productCoordinateRing (k := k) f))))

#print axioms geometricKahlerFiberEquiv_single
#print axioms geometricCotangentTowerEquiv_single
/-- The quotient naturality square commutes on the complete
finite free coordinate module, extending its generator calculation.
The bottom map is the *independently defined* coordinate extension
followed by the original-Jacobian quotient. -/
theorem geometricCotangentTower_coordinate_square
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    (geometricCotangentTowerEquiv f u hu φ).toLinearMap.comp
      ((Submodule.mkQ (Deligne21G.geometricConormalRelations f u)).baseChange M) =
    (Submodule.mkQ
      (Deligne21G.geometricConormalRelations f (fun j => φ (u j)))).comp
      (fieldTowerCoordinateEquiv (ι := Deligne16.Coord k s) φ).toLinearMap := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  classical
  apply ((Pi.basisFun L (Deligne16.Coord k s)).baseChange M).ext
  intro i
  simp only [Basis.baseChange_apply, Pi.basisFun_apply]
  change geometricCotangentTowerEquiv f u hu φ
      (((Submodule.mkQ (Deligne21G.geometricConormalRelations f u)).baseChange M)
        ((1 : M) ⊗ₜ[L] Pi.single i (1 : L))) =
    (Submodule.mkQ
      (Deligne21G.geometricConormalRelations f (fun j => φ (u j))))
      (fieldTowerCoordinateEquiv (ι := Deligne16.Coord k s) φ
        ((1 : M) ⊗ₜ[L] Pi.single i (1 : L)))
  rw [LinearMap.baseChange_tmul]
  rw [fieldTowerCoordinateEquiv_single]
  simpa only [Submodule.mkQ_apply] using
    (geometricCotangentTowerEquiv_single f u hu φ i)

/-- The original polynomial-Jacobian tangent is preserved
coordinatewise by arbitrary field homomorphisms over K.
This includes positive-characteristic inseparable towers and
Frobenius maps wherever the indicated algebra maps exist. -/
theorem geometricJacobianTangent_map_mem
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u v : Deligne16.Coord k s → L)
    (φ : L →ₐ[K] M)
    (hv : v ∈ Deligne21G.geometricJacobianTangent f u) :
    (fun i => φ (v i)) ∈ Deligne21G.geometricJacobianTangent f
      (fun i => φ (u i)) := by
  classical
  apply (Deligne21G.mem_geometricJacobianTangent_iff f
    (fun i => φ (u i)) (fun i => φ (v i))).mpr
  intro t
  have ht := (Deligne21G.mem_geometricJacobianTangent_iff f u v).mp hv t
  calc
    (∑ i : Deligne16.Coord k s,
        Deligne21G.geometricConormalRow f (fun j => φ (u j)) t i * φ (v i)) =
      ∑ i : Deligne16.Coord k s,
        φ (Deligne21G.geometricConormalRow f u t i * v i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Deligne21G.geometricConormalRow_map, map_mul]
    _ = φ (∑ i : Deligne16.Coord k s,
          Deligne21G.geometricConormalRow f u t i * v i) := by rw [map_sum]
    _ = 0 := by rw [ht, map_zero]

/-- Field homomorphisms preserve the evaluation pairing that
identifies the original conormal quotient dual with its Jacobian
tangent in DEL-21G. -/
theorem geometricCoordinatePairing_map
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s : ℕ} (φ : L →ₐ[K] M)
    (v w : Deligne16.Coord k s → L) :
    (∑ i : Deligne16.Coord k s, φ (v i) * φ (w i)) =
      φ (∑ i : Deligne16.Coord k s, v i * w i) := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]

/-- Full pure-tensor formula for the original-ideal cotangent
quotient under field extension. A scalar in M multiplies the
coordinatewise image of the L-valued representative. -/
theorem geometricCotangentTowerEquiv_tmul
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M)
    (m : M) (v : Deligne16.Coord k s → L) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    geometricCotangentTowerEquiv f u hu φ
      (m ⊗ₜ[L] (Submodule.Quotient.mk v)) =
      Submodule.Quotient.mk (fun i => m * φ (v i)) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  classical
  have h := LinearMap.congr_fun
    (geometricCotangentTower_coordinate_square f u hu φ) (m ⊗ₜ[L] v)
  have hc : fieldTowerCoordinateEquiv (ι := Deligne16.Coord k s) φ
      (m ⊗ₜ[L] v) = fun i => m * φ (v i) := by
    rw [tmul_eq_smul_one_tmul]
    ext i
    simp only [map_smul, Pi.smul_apply, smul_eq_mul,
      fieldTowerCoordinateEquiv_one_tmul]
  simpa only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
    Submodule.mkQ_apply, hc] using h

/-- At L=K the original (possibly nonreduced) conormal span is
literally the DEL-21D conormal subspace. -/
theorem geometricConormalRelations_self
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K) :
    Deligne21G.geometricConormalRelations f u =
      Deligne21D.conormalRelations f u := by
  change Submodule.span K (Set.range (Deligne21G.geometricConormalRow f u)) =
    Submodule.span K (Set.range (Deligne21D.conormalRow f u))
  have hrows : Deligne21G.geometricConormalRow f u =
      Deligne21D.conormalRow f u := by
    funext t
    exact Deligne21G.geometricConormalRow_self f u t
  rw [hrows]

/-- The coordinate presentation of the geometric cotangent fiber
specializes, by the actual original ideal, to DEL-21D's base-field
Jacobian quotient. -/
noncomputable def geometricCotangentSelfEquiv
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K) :
    Deligne21G.geometricCotangentFiber f u ≃ₗ[K]
      Deligne21D.presentedCotangentFiber f u :=
  Submodule.quotEquivOfEq _ _ (geometricConormalRelations_self f u)

/-- The L=K comparison is the identity on classes of every
coordinate representative, not just a dimension equality. -/
theorem geometricCotangentSelfEquiv_mk
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u v : Deligne16.Coord k s → K) :
    geometricCotangentSelfEquiv f u
      (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  exact Submodule.quotEquivOfEq_mk _ _ (geometricConormalRelations_self f u) v

#print axioms geometricCotangentTowerEquiv_tmul
#print axioms geometricConormalRelations_self
#print axioms geometricCotangentSelfEquiv_mk
/-- Dualizing the verified cotangent field-tower equivalence
gives an actual M-linear extension-of-scalars equivalence for the
original polynomial Jacobian tangent. The finite-dimensional dual
base-change map is Mathlib's `IsBaseChange.toDualBaseChange`, and
each tangent is identified with the genuine quotient-dual using
DEL-21G's Jacobian duality theorem. -/
noncomputable def geometricJacobianTangentTowerEquiv
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ} (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    M ⊗[L] Deligne21G.geometricJacobianTangent f u ≃ₗ[M]
      Deligne21G.geometricJacobianTangent f (fun i => φ (u i)) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  let eQ := geometricCotangentTowerEquiv f u hu φ
  let j : Deligne21G.geometricCotangentFiber f u →ₗ[L]
      Deligne21G.geometricCotangentFiber f (fun i => φ (u i)) :=
    (eQ.toLinearMap.restrictScalars L).comp
      (TensorProduct.mk L M (Deligne21G.geometricCotangentFiber f u) 1)
  have hb : IsBaseChange M j :=
    IsBaseChange.of_equiv eQ (by intro x; rfl)
  let eL := Deligne21G.geometricCotangentDualEquivTangent f u
  let eM := Deligne21G.geometricCotangentDualEquivTangent f (fun i => φ (u i))
  exact (eL.symm.baseChange L M _ _).trans (hb.toDualBaseChange.trans eM)

#print axioms geometricJacobianTangentTowerEquiv
#print axioms geometricCotangentTower_coordinate_square
#print axioms geometricJacobianTangent_map_mem
#print axioms geometricCoordinatePairing_map
#print axioms geometricPoint_tower
#print axioms geometricKahlerCancelBaseChange_tmul

end Deligne21H

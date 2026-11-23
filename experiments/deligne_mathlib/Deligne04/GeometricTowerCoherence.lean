import Deligne04.GeometricFiberCoherence
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic

/-!
# DEL-21J: three-field tower coherence for original-scheme cotangent and tangent fibers

The quotient algebra, Kähler differential presentation, and Jacobian rows
are those of the full original DEL-16 lifted ideal. No reducedness or
separability assumption is introduced.
-/

open TensorProduct Module

namespace Deligne21J

/-- The algebra structures induced by compatible K-algebra field maps form
a genuine three-field scalar tower. -/
theorem fieldTower_scalar
    {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    (φ : L →ₐ[K] M) (ψ : M →ₐ[K] N) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    letI : Algebra M N := ψ.toRingHom.toAlgebra
    letI : Algebra L N := (ψ.comp φ).toRingHom.toAlgebra
    IsScalarTower L M N := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  letI : Algebra M N := ψ.toRingHom.toAlgebra
  letI : Algebra L N := (ψ.comp φ).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

/-- The real tensor-product associator for the field tower, in its
cancellation orientation. -/
noncomputable def fieldTowerCancelBaseChange
    {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    (φ : L →ₐ[K] M) (ψ : M →ₐ[K] N)
    (V : Type*) [AddCommMonoid V] [Module L V] :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    letI : Algebra M N := ψ.toRingHom.toAlgebra
    letI : Algebra L N := (ψ.comp φ).toRingHom.toAlgebra
    N ⊗[M] (M ⊗[L] V) ≃ₗ[N] N ⊗[L] V := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  letI : Algebra M N := ψ.toRingHom.toAlgebra
  letI : Algebra L N := (ψ.comp φ).toRingHom.toAlgebra
  letI : IsScalarTower L M N := fieldTower_scalar φ ψ
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange L M N N V

/-- DEL-21I's genuine dual-defined tangent isomorphism acts on every
pure tensor, by M-linearity of the already-verified one-tensor formula. -/
theorem geometricJacobianTangentTowerEquiv_tmul
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M)
    (m : M) (v : Deligne21G.geometricJacobianTangent f u) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    (Deligne21H.geometricJacobianTangentTowerEquiv f u hu φ)
      (m ⊗ₜ[L] v) =
        m • (⟨fun i => φ ((v : Deligne16.Coord k s → L) i),
          Deligne21H.geometricJacobianTangent_map_mem f u
            (v : Deligne16.Coord k s → L) φ v.property⟩ :
          Deligne21G.geometricJacobianTangent f (fun i => φ (u i))) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  calc
    _ = (Deligne21H.geometricJacobianTangentTowerEquiv f u hu φ)
          (m • ((1 : M) ⊗ₜ[L] v)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = m • (Deligne21H.geometricJacobianTangentTowerEquiv f u hu φ)
          ((1 : M) ⊗ₜ[L] v) := map_smul _ _ _
    _ = _ := by rw [Deligne21I.geometricJacobianTangentTowerEquiv_one_tmul]

/-- Its image has the familiar explicit coordinate formula. -/
theorem geometricJacobianTangentTowerEquiv_tmul_coord
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M)
    (m : M) (v : Deligne21G.geometricJacobianTangent f u)
    (i : Deligne16.Coord k s) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    (((Deligne21H.geometricJacobianTangentTowerEquiv f u hu φ)
      (m ⊗ₜ[L] v) : Deligne21G.geometricJacobianTangent f (fun i => φ (u i))) :
        Deligne16.Coord k s → M) i =
      m * φ ((v : Deligne16.Coord k s → L) i) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  rw [geometricJacobianTangentTowerEquiv_tmul]
  rfl

/-- The original Kähler-defined cotangent extension agrees on every
coordinate representative with the independently proven full linear-map
coordinate naturality square from DEL-21H. -/
theorem geometricCotangentTowerEquiv_one_tmul_mk
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M)
    (v : Deligne16.Coord k s → L) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    (Deligne21H.geometricCotangentTowerEquiv f u hu φ)
      ((1 : M) ⊗ₜ[L] (Submodule.Quotient.mk v)) =
      Submodule.Quotient.mk (fun i => φ (v i)) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  classical
  have hs := Deligne21H.geometricCotangentTower_coordinate_square f u hu φ
  have heq := congrArg
    (fun h => h ((1 : M) ⊗ₜ[L] v)) hs
  have hcoord :
      Deligne21H.fieldTowerCoordinateEquiv (ι := Deligne16.Coord k s) φ
        ((1 : M) ⊗ₜ[L] v) =
        (fun i => φ (v i)) := by
    ext i
    exact Deligne21H.fieldTowerCoordinateEquiv_one_tmul φ v i
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
    Submodule.mkQ_apply] at heq
  exact heq.trans (congrArg
    (fun w : Deligne16.Coord k s → M =>
      (Submodule.Quotient.mk w :
        Deligne21G.geometricCotangentFiber f (fun i => φ (u i)))) hcoord)

/-- Arbitrary pure tensors of an original coordinate quotient class
are transported by scalar extension and the field-homomorphic coordinates. -/
theorem geometricCotangentTowerEquiv_tmul_mk
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M)
    (m : M) (v : Deligne16.Coord k s → L) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    (Deligne21H.geometricCotangentTowerEquiv f u hu φ)
      (m ⊗ₜ[L] Submodule.Quotient.mk v) =
      m • Submodule.Quotient.mk (fun i => φ (v i)) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  calc
    _ = (Deligne21H.geometricCotangentTowerEquiv f u hu φ)
          (m • ((1 : M) ⊗ₜ[L] Submodule.Quotient.mk v)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = m • (Deligne21H.geometricCotangentTowerEquiv f u hu φ)
          ((1 : M) ⊗ₜ[L] Submodule.Quotient.mk v) := map_smul _ _ _
    _ = _ := by rw [geometricCotangentTowerEquiv_one_tmul_mk]


/-- A general composition principle for true extension-of-scalars
linear equivalences. Equality on all original unit tensors forces
equality on the whole doubly base-changed module, after the canonical
Mathlib tensor reassociation. -/
theorem towerEquiv_comp_of_one_tmul
    {L M N : Type*} [Field L] [Field M] [Field N]
    [Algebra L M] [Algebra M N] [Algebra L N] [IsScalarTower L M N]
    {V W X : Type*}
    [AddCommGroup V] [Module L V]
    [AddCommGroup W] [Module M W]
    [AddCommGroup X] [Module N X]
    (eLM : M ⊗[L] V ≃ₗ[M] W)
    (eMN : N ⊗[M] W ≃ₗ[N] X)
    (eLN : N ⊗[L] V ≃ₗ[N] X)
    (h : ∀ v : V,
      eLN ((1 : N) ⊗ₜ[L] v) =
        eMN ((1 : N) ⊗ₜ[M] eLM ((1 : M) ⊗ₜ[L] v))) :
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange L M N N V).trans eLN) =
      ((eLM.baseChange M N _ _).trans eMN) := by
  have hscalar (a : N) (v : V) :
      eLN (a ⊗ₜ[L] v) =
        eMN (a ⊗ₜ[M] eLM ((1 : M) ⊗ₜ[L] v)) := by
    calc
      eLN (a ⊗ₜ[L] v) =
          a • eLN ((1 : N) ⊗ₜ[L] v) := by
            rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = a • eMN ((1 : N) ⊗ₜ[M] eLM ((1 : M) ⊗ₜ[L] v)) :=
          congrArg (fun x : X => a • x) (h v)
      _ = eMN (a ⊗ₜ[M] eLM ((1 : M) ⊗ₜ[L] v)) := by
            rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hmiddle (m : M) (v : V) :
      eLM (m ⊗ₜ[L] v) = m • eLM ((1 : M) ⊗ₜ[L] v) := by
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a w =>
      induction w using TensorProduct.inductionOn with
      | add x y hx hy =>
          simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hx hy
      | tmul m v =>
          simp only [LinearEquiv.trans_apply,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            LinearEquiv.baseChange_tmul]
          rw [hmiddle, TensorProduct.tmul_smul]
          exact hscalar (m • a) v

/-- Composition of the genuine DEL-21H dual-defined Jacobian tangent
extension maps in a three-stage field tower, as equality of entire
N-linear equivalences after canonical tensor reassociation. -/
theorem geometricJacobianTangentTower_comp
    {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M) (ψ : M →ₐ[K] N) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    letI : Algebra M N := ψ.toRingHom.toAlgebra
    letI : Algebra L N := (ψ.comp φ).toRingHom.toAlgebra
    (fieldTowerCancelBaseChange φ ψ
        (Deligne21G.geometricJacobianTangent f u)).trans
      (Deligne21H.geometricJacobianTangentTowerEquiv f u hu (ψ.comp φ)) =
    ((Deligne21H.geometricJacobianTangentTowerEquiv f u hu φ).baseChange M N _ _).trans
      (Deligne21H.geometricJacobianTangentTowerEquiv f (fun i => φ (u i))
        (Deligne21G.onGeometricProduct_map f u hu φ) ψ) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  letI : Algebra M N := ψ.toRingHom.toAlgebra
  letI : Algebra L N := (ψ.comp φ).toRingHom.toAlgebra
  letI : IsScalarTower L M N := fieldTower_scalar φ ψ
  let eLM := Deligne21H.geometricJacobianTangentTowerEquiv f u hu φ
  let eMN := Deligne21H.geometricJacobianTangentTowerEquiv f
    (fun i => φ (u i)) (Deligne21G.onGeometricProduct_map f u hu φ) ψ
  let eLN := Deligne21H.geometricJacobianTangentTowerEquiv f u hu (ψ.comp φ)
  have hunit (v : Deligne21G.geometricJacobianTangent f u) :
      eLN ((1 : N) ⊗ₜ[L] v) =
        eMN ((1 : N) ⊗ₜ[M] eLM ((1 : M) ⊗ₜ[L] v)) := by
    apply Subtype.ext
    funext i
    rw [Deligne21I.geometricJacobianTangentTowerEquiv_one_tmul
      f u hu (ψ.comp φ) v]
    rw [Deligne21I.geometricJacobianTangentTowerEquiv_one_tmul
      f (fun j => φ (u j)) (Deligne21G.onGeometricProduct_map f u hu φ)
        ψ (eLM ((1 : M) ⊗ₜ[L] v))]
    rw [Deligne21I.geometricJacobianTangentTowerEquiv_one_tmul f u hu φ v]
    rfl
  change ((TensorProduct.AlgebraTensorModule.cancelBaseChange L M N N
      (Deligne21G.geometricJacobianTangent f u)).trans eLN) =
    ((eLM.baseChange M N _ _).trans eMN)
  exact towerEquiv_comp_of_one_tmul eLM eMN eLN hunit

/-- Composition of the actual Kähler-defined DEL-21H cotangent
extension maps, through the true tensor associator, as an equality
on the full conormal quotient. -/
theorem geometricCotangentTower_comp
    {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M) (ψ : M →ₐ[K] N) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    letI : Algebra M N := ψ.toRingHom.toAlgebra
    letI : Algebra L N := (ψ.comp φ).toRingHom.toAlgebra
    (fieldTowerCancelBaseChange φ ψ
        (Deligne21G.geometricCotangentFiber f u)).trans
      (Deligne21H.geometricCotangentTowerEquiv f u hu (ψ.comp φ)) =
    ((Deligne21H.geometricCotangentTowerEquiv f u hu φ).baseChange M N _ _).trans
      (Deligne21H.geometricCotangentTowerEquiv f (fun i => φ (u i))
        (Deligne21G.onGeometricProduct_map f u hu φ) ψ) := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  letI : Algebra M N := ψ.toRingHom.toAlgebra
  letI : Algebra L N := (ψ.comp φ).toRingHom.toAlgebra
  letI : IsScalarTower L M N := fieldTower_scalar φ ψ
  let eLM := Deligne21H.geometricCotangentTowerEquiv f u hu φ
  let eMN := Deligne21H.geometricCotangentTowerEquiv f
    (fun i => φ (u i)) (Deligne21G.onGeometricProduct_map f u hu φ) ψ
  let eLN := Deligne21H.geometricCotangentTowerEquiv f u hu (ψ.comp φ)
  have hunit (q : Deligne21G.geometricCotangentFiber f u) :
      eLN ((1 : N) ⊗ₜ[L] q) =
        eMN ((1 : N) ⊗ₜ[M] eLM ((1 : M) ⊗ₜ[L] q)) := by
    obtain ⟨v, rfl⟩ :=
      Submodule.Quotient.mk_surjective (Deligne21G.geometricConormalRelations f u) q
    rw [geometricCotangentTowerEquiv_one_tmul_mk f u hu (ψ.comp φ) v]
    rw [geometricCotangentTowerEquiv_one_tmul_mk f u hu φ v]
    rw [geometricCotangentTowerEquiv_one_tmul_mk f
      (fun i => φ (u i)) (Deligne21G.onGeometricProduct_map f u hu φ)
      ψ (fun i => φ (v i))]
    rfl
  change ((TensorProduct.AlgebraTensorModule.cancelBaseChange L M N N
      (Deligne21G.geometricCotangentFiber f u)).trans eLN) =
    ((eLM.baseChange M N _ _).trans eMN)
  exact towerEquiv_comp_of_one_tmul eLM eMN eLN hunit


#print axioms towerEquiv_comp_of_one_tmul
#print axioms geometricJacobianTangentTower_comp
#print axioms geometricCotangentTower_comp

#print axioms fieldTower_scalar
#print axioms fieldTowerCancelBaseChange
#print axioms geometricJacobianTangentTowerEquiv_tmul
#print axioms geometricJacobianTangentTowerEquiv_tmul_coord
#print axioms geometricCotangentTowerEquiv_one_tmul_mk
#print axioms geometricCotangentTowerEquiv_tmul_mk

end Deligne21J

import Deligne04.GeometricTowerCoherence
import Mathlib.Tactic

/-!
# DEL-21K: identity-field normalization for the actual Kähler and tangent fibers

For the identity K-algebra map of L, the DEL-21H canonical Kähler
extension and its dual-defined tangent equivalence are the tensor left
unit, on the complete quotient and tangent modules. The underlying
coordinate algebra retains every original DEL-16 lifted relation.
-/

open TensorProduct Module

namespace Deligne21K

/-- The L-valued point obtained by the identity K-algebra map is the
original point, coordinate by coordinate. -/
theorem geometricPoint_identity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s : ℕ} (u : Deligne16.Coord k s → L) :
    (fun i => (AlgHom.id K L) (u i)) = u := by
  funext i
  rfl

/-- The cotangent target of identity-field transport uses precisely
the original conormal subspace. This also holds on nonreduced fibers. -/
theorem geometricConormalRelations_identity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L) :
    Deligne21G.geometricConormalRelations f
      (fun i => (AlgHom.id K L) (u i)) =
        Deligne21G.geometricConormalRelations f u := by
  rw [geometricPoint_identity u]

/-- In an ordinary self-extension, agreement on unit tensors
determines a linear equivalence on the whole tensor product. -/
theorem tensorLid_ext
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
    (e : R ⊗[R] V ≃ₗ[R] V)
    (h : ∀ v : V, e ((1 : R) ⊗ₜ[R] v) = v) :
    e = TensorProduct.lid R V := by
  apply LinearEquiv.ext
  intro z
  calc
    e z = e ((TensorProduct.lid R V).symm
        ((TensorProduct.lid R V) z)) := by
          rw [LinearEquiv.symm_apply_apply]
    _ = e ((1 : R) ⊗ₜ[R] ((TensorProduct.lid R V) z)) := by
          rw [TensorProduct.lid_symm_apply]
    _ = (TensorProduct.lid R V) z := h _

/-- Original Kähler cotangent transport through the identity
K-algebra morphism agrees on every coordinate quotient class. -/
theorem geometricCotangentTower_identity_tmul_mk
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (m : L) (v : Deligne16.Coord k s → L) :
    letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
    (Deligne21H.geometricCotangentTowerEquiv f u hu (AlgHom.id K L))
      (m ⊗ₜ[L] Submodule.Quotient.mk v) =
        m • (Submodule.Quotient.mk v :
          Deligne21G.geometricCotangentFiber f u) := by
  letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
  have h := Deligne21J.geometricCotangentTowerEquiv_tmul_mk f u hu
    (AlgHom.id K L) m v
  rw [geometricPoint_identity u] at h
  rw [geometricPoint_identity v] at h
  exact h

/-- The DEL-21H dual-defined tangent identity transport evaluates as
ordinary scalar multiplication on every pure tensor. -/
theorem geometricJacobianTangentTower_identity_tmul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (m : L) (v : Deligne21G.geometricJacobianTangent f u) :
    letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
    (Deligne21H.geometricJacobianTangentTowerEquiv f u hu (AlgHom.id K L))
      (m ⊗ₜ[L] v) = m • v := by
  letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
  have h := Deligne21J.geometricJacobianTangentTowerEquiv_tmul
    f u hu (AlgHom.id K L) m v
  rw [geometricPoint_identity u] at h
  rw [h]
  apply Subtype.ext
  funext i
  rfl

/-- The existing DEL-21H Kähler base-change equivalence along the
identity field morphism is the full tensor left-unit isomorphism. -/
theorem geometricCotangentTower_identity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u) :
    letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
    Deligne21H.geometricCotangentTowerEquiv f u hu (AlgHom.id K L) =
      TensorProduct.lid L (Deligne21G.geometricCotangentFiber f u) := by
  letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
  classical
  apply tensorLid_ext
  intro q
  obtain ⟨v, rfl⟩ :=
    Submodule.Quotient.mk_surjective (Deligne21G.geometricConormalRelations f u) q
  simpa only [one_smul] using
    (geometricCotangentTower_identity_tmul_mk f u hu (1 : L) v)

/-- The existing DEL-21H dual-defined tangent extension agrees
with tensor lid on the entire original Jacobian tangent submodule. -/
theorem geometricJacobianTangentTower_identity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u) :
    letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
    Deligne21H.geometricJacobianTangentTowerEquiv f u hu (AlgHom.id K L) =
      TensorProduct.lid L (Deligne21G.geometricJacobianTangent f u) := by
  letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
  classical
  apply tensorLid_ext
  intro v
  simpa only [one_smul] using
    (geometricJacobianTangentTower_identity_tmul f u hu (1 : L) v)

#print axioms geometricPoint_identity
#print axioms geometricConormalRelations_identity
#print axioms geometricCotangentTower_identity_tmul_mk
#print axioms geometricJacobianTangentTower_identity_tmul
#print axioms geometricCotangentTower_identity
#print axioms geometricJacobianTangentTower_identity

end Deligne21K

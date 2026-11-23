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

/-- The exact original quotient conormal presentation gives a
canonical identification of the identity-field target with Q_u. -/
noncomputable def geometricCotangentIdentityTargetEquiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L) :
    Deligne21G.geometricCotangentFiber f
      (fun i => (AlgHom.id K L) (u i)) ≃ₗ[L]
        Deligne21G.geometricCotangentFiber f u :=
  Submodule.quotEquivOfEq _ _ (geometricConormalRelations_identity f u)

/-- The quotient target identification fixes the class of every
original finite coordinate representative. -/
theorem geometricCotangentIdentityTargetEquiv_mk
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u v : Deligne16.Coord k s → L) :
    geometricCotangentIdentityTargetEquiv f u
        (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  exact Submodule.quotEquivOfEq_mk _ _
    (geometricConormalRelations_identity f u) v

/-- The original Jacobian tangent subspace at the identity-transported
point is exactly the original subspace, including all scheme relations. -/
theorem geometricJacobianTangent_identity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L) :
    Deligne21G.geometricJacobianTangent f
      (fun i => (AlgHom.id K L) (u i)) =
        Deligne21G.geometricJacobianTangent f u := by
  rw [geometricPoint_identity u]

/-- The canonical equality-of-subspaces equivalence carries the
identity-field target tangent back to its original representation. -/
noncomputable def geometricJacobianTangentIdentityTargetEquiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L) :
    Deligne21G.geometricJacobianTangent f
      (fun i => (AlgHom.id K L) (u i)) ≃ₗ[L]
        Deligne21G.geometricJacobianTangent f u :=
  LinearEquiv.ofEq _ _ (geometricJacobianTangent_identity f u)

/-- Normalize DEL-21H's original-ideal Kähler equivalence through
the proved equality of the identity-field conormal quotients. -/
noncomputable def geometricCotangentIdentityTransport
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u) :
    letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
    L ⊗[L] Deligne21G.geometricCotangentFiber f u ≃ₗ[L]
      Deligne21G.geometricCotangentFiber f u := by
  letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
  exact (Deligne21H.geometricCotangentTowerEquiv f u hu (AlgHom.id K L)).trans
    (geometricCotangentIdentityTargetEquiv f u)

/-- Normalize DEL-21H's actual dual-defined Jacobian tangent equivalence
via the literal equality of the identity-field tangent subspaces. -/
noncomputable def geometricJacobianTangentIdentityTransport
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u) :
    letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
    L ⊗[L] Deligne21G.geometricJacobianTangent f u ≃ₗ[L]
      Deligne21G.geometricJacobianTangent f u := by
  letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
  exact (Deligne21H.geometricJacobianTangentTowerEquiv f u hu (AlgHom.id K L)).trans
    (geometricJacobianTangentIdentityTargetEquiv f u)

/-- On every original quotient class, normalized identity-field Kähler
transport is the tensor left-unit formula. -/
theorem geometricCotangentIdentityTransport_tmul_mk
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (m : L) (v : Deligne16.Coord k s → L) :
    letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
    geometricCotangentIdentityTransport f u hu
      (m ⊗ₜ[L] Submodule.Quotient.mk v) =
        m • (Submodule.Quotient.mk v :
          Deligne21G.geometricCotangentFiber f u) := by
  letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
  change (geometricCotangentIdentityTargetEquiv f u)
    ((Deligne21H.geometricCotangentTowerEquiv f u hu (AlgHom.id K L))
      (m ⊗ₜ[L] Submodule.Quotient.mk v)) = _
  rw [Deligne21J.geometricCotangentTowerEquiv_tmul_mk]
  rw [map_smul, geometricCotangentIdentityTargetEquiv_mk]
  rw [geometricPoint_identity v]

/-- The normalized dual tangent identity transport acts as ordinary
scalar multiplication, on each pure tensor of original tangent vectors. -/
theorem geometricJacobianTangentIdentityTransport_tmul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (m : L) (v : Deligne21G.geometricJacobianTangent f u) :
    letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
    geometricJacobianTangentIdentityTransport f u hu
      (m ⊗ₜ[L] v) = m • v := by
  letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
  change (geometricJacobianTangentIdentityTargetEquiv f u)
    ((Deligne21H.geometricJacobianTangentTowerEquiv f u hu (AlgHom.id K L))
      (m ⊗ₜ[L] v)) = _
  rw [Deligne21J.geometricJacobianTangentTowerEquiv_tmul]
  rw [map_smul]
  apply Subtype.ext
  funext i
  simp only [geometricJacobianTangentIdentityTargetEquiv,
    LinearEquiv.coe_ofEq_apply, AlgHom.id_apply, Pi.smul_apply,
    SetLike.val_smul, smul_eq_mul]

/-- The true original-ideal Kähler field-extension equivalence along
identity, after its canonical target equality, is exactly tensor lid on
the *entire* quotient. -/
theorem geometricCotangentTower_identity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u) :
    letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
    geometricCotangentIdentityTransport f u hu =
      TensorProduct.lid L (Deligne21G.geometricCotangentFiber f u) := by
  letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
  classical
  apply tensorLid_ext
  intro q
  obtain ⟨v, rfl⟩ :=
    Submodule.Quotient.mk_surjective (Deligne21G.geometricConormalRelations f u) q
  simpa only [one_smul] using
    (geometricCotangentIdentityTransport_tmul_mk f u hu (1 : L) v)

/-- The dual-defined DEL-21H Jacobian tangent identity map, through
its canonical target-subspace equality, is tensor lid on the *entire*
tangent module. -/
theorem geometricJacobianTangentTower_identity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u) :
    letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
    geometricJacobianTangentIdentityTransport f u hu =
      TensorProduct.lid L (Deligne21G.geometricJacobianTangent f u) := by
  letI : Algebra L L := (AlgHom.id K L).toRingHom.toAlgebra
  classical
  apply tensorLid_ext
  intro v
  simpa only [one_smul] using
    (geometricJacobianTangentIdentityTransport_tmul f u hu (1 : L) v)

#print axioms geometricPoint_identity
#print axioms geometricConormalRelations_identity
#print axioms geometricCotangentTower_identity_tmul_mk
#print axioms geometricJacobianTangentTower_identity_tmul
#print axioms geometricCotangentTower_identity
#print axioms geometricJacobianTangentTower_identity

end Deligne21K

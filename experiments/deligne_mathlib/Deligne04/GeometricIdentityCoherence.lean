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

/-- On each original coordinate class the genuine DEL-21H Kähler
base-change map along the identity field morphism acts as tensor lid. -/
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
  simpa only [AlgHom.id_apply] using
    (Deligne21J.geometricCotangentTowerEquiv_tmul_mk f u hu
      (AlgHom.id K L) m v)

/-- The dual-defined DEL-21H Jacobian-tangent extension on the identity
map is scalar multiplication, on every original pure tensor. -/
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
  apply Subtype.ext
  funext i
  simpa only [AlgHom.id_apply, SetLike.val_smul, Pi.smul_apply,
    smul_eq_mul] using congrArg
      (fun x : Deligne21G.geometricJacobianTangent f
        (fun j => (AlgHom.id K L) (u j)) =>
        (x : Deligne16.Coord k s → L) i) h

/-- Identity-field transport on the *entire* original Kähler cotangent
quotient is the tensor left-unit equivalence. -/
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
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      calc
        _ = (Deligne21H.geometricCotangentTowerEquiv f u hu (AlgHom.id K L)) x +
            (Deligne21H.geometricCotangentTowerEquiv f u hu (AlgHom.id K L)) y :=
              map_add _ x y
        _ = (TensorProduct.lid L (Deligne21G.geometricCotangentFiber f u)) x +
            (TensorProduct.lid L (Deligne21G.geometricCotangentFiber f u)) y :=
              congrArg₂ (· + ·) hx hy
        _ = (TensorProduct.lid L (Deligne21G.geometricCotangentFiber f u)) (x+y) :=
              (map_add _ x y).symm
  | tmul m q =>
      obtain ⟨v, rfl⟩ :=
        Submodule.Quotient.mk_surjective (Deligne21G.geometricConormalRelations f u) q
      simpa only [TensorProduct.lid_tmul] using
        (geometricCotangentTower_identity_tmul_mk f u hu m v)

/-- Identity-field transport on the *entire* original Jacobian tangent
submodule agrees with tensor lid, without choosing a quotient basis. -/
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
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      calc
        _ = (Deligne21H.geometricJacobianTangentTowerEquiv f u hu (AlgHom.id K L)) x +
            (Deligne21H.geometricJacobianTangentTowerEquiv f u hu (AlgHom.id K L)) y :=
              map_add _ x y
        _ = (TensorProduct.lid L (Deligne21G.geometricJacobianTangent f u)) x +
            (TensorProduct.lid L (Deligne21G.geometricJacobianTangent f u)) y :=
              congrArg₂ (· + ·) hx hy
        _ = (TensorProduct.lid L (Deligne21G.geometricJacobianTangent f u)) (x+y) :=
              (map_add _ x y).symm
  | tmul m v =>
      simpa only [TensorProduct.lid_tmul] using
        (geometricJacobianTangentTower_identity_tmul f u hu m v)

#print axioms geometricPoint_identity
#print axioms geometricConormalRelations_identity
#print axioms geometricCotangentTower_identity_tmul_mk
#print axioms geometricJacobianTangentTower_identity_tmul
#print axioms geometricCotangentTower_identity
#print axioms geometricJacobianTangentTower_identity

end Deligne21K

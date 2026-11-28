import Deligne04.DualNumberSchemeTangent
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic

/-!
# DEL-21B: Kähler differentials and square-zero lifts

Mathlib proves two universal properties:
  Hom_A(Ω[A/R], M) ≃ Der_R(A,M), and
  Der_R(A,I) ≃ algebra lifts A -> B across a square-zero ideal I in B.

We compose these genuine linear/equivalence maps into an explicit
Kähler-to-infinitesimal-lifts interface. We also specialize the
square-zero ideal to the actual nilpotent ideal in DualNumber K,
and construct the constant dual-number lift of an arbitrary
K-rational point of a K-algebra.

The later U^k-specific target is to prove that the Kähler
functional, derivation, and DEL-21A polynomial Jacobian tangent
represent the *same* tangent in natural coordinates. That
requires identifying the point-induced module structure and the
actual quotient of the full presentation ideal, then transporting
the Mathlib equivalence. The global relative Bertini incidence
and Katz weak Lefschetz remain separate.
-/

namespace Deligne21B

universe u v w

/-- Compose the Kähler universal derivation with Mathlib's
equivalence between derivations into a square-zero ideal and
algebra lifts through the ideal's quotient. -/
noncomputable def kahlerSquareZeroLiftEquiv
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    (I : Ideal B) (hI : I ^ 2 = ⊥) :
    (Ω[A⁄R] →ₗ[A] I) ≃
      {f : A →ₐ[R] B //
        (Ideal.Quotient.mkₐ R I).comp f =
          IsScalarTower.toAlgHom R A (B ⧸ I)} :=
  (KaehlerDifferential.linearMapEquivDerivation R A).toEquiv.trans
    (derivationToSquareZeroEquivLift I hI)

/-- The actual nilpotent ideal in dual numbers is a square-zero
ideal, in every characteristic, with a pinned Mathlib proof. -/
theorem dualNumberNilpotentIdeal_square
    (K : Type*) [Field K] :
    (TrivSqZeroExt.kerIdeal K K) ^ 2 = ⊥ :=
  TrivSqZeroExt.kerIdeal_sq K K

/-- Every K-rational point of an arbitrary affine K-algebra A
defines a canonical constant first-order algebra map to dual
numbers. -/
noncomputable def constantDualNumberLift
    {K : Type*} [Field K] {A : Type*}
    [CommRing A] [Algebra K A]
    (point : A →ₐ[K] K) : A →ₐ[K] DualNumber K :=
  (TrivSqZeroExt.inlAlgHom K K K).comp point

/-- The constant lift reduces to the original point under the
dual-number projection to K. -/
theorem fst_constantDualNumberLift
    {K : Type*} [Field K] {A : Type*}
    [CommRing A] [Algebra K A]
    (point : A →ₐ[K] K) :
    (TrivSqZeroExt.fstHom K K K).comp
      (constantDualNumberLift point) = point := by
  ext x
  rfl

/-- The algebra structure on the dual numbers induced by the
constant lift of the K-rational point. -/
noncomputable def pointDualNumberAlgebra
    {K : Type*} [Field K] {A : Type*}
    [CommRing A] [Algebra K A]
    (point : A →ₐ[K] K) : Algebra A (DualNumber K) :=
  (constantDualNumberLift point).toRingHom.toAlgebra

/-- The Kähler-to-square-zero equivalence specialized to the
actual dual-number ideal at any prescribed K-rational point.
The local algebra structure on DualNumber K comes from that point. -/
noncomputable def kahlerDualNumberLiftAtPoint
    {K : Type*} [Field K] {A : Type*}
    [CommRing A] [Algebra K A]
    (point : A →ₐ[K] K) :
    letI : Algebra A (DualNumber K) := pointDualNumberAlgebra point
    letI : IsScalarTower K A (DualNumber K) :=
      IsScalarTower.of_algebraMap_eq'
        (constantDualNumberLift point).comp_algebraMap.symm
    (Ω[A⁄K] →ₗ[A] TrivSqZeroExt.kerIdeal K K) ≃
      {f : A →ₐ[K] DualNumber K //
        (Ideal.Quotient.mkₐ K (TrivSqZeroExt.kerIdeal K K)).comp f =
          IsScalarTower.toAlgHom K A
            (DualNumber K ⧸ TrivSqZeroExt.kerIdeal K K)} := by
  letI : Algebra A (DualNumber K) := pointDualNumberAlgebra point
  letI : IsScalarTower K A (DualNumber K) :=
    IsScalarTower.of_algebraMap_eq'
      (constantDualNumberLift point).comp_algebraMap.symm
  exact kahlerSquareZeroLiftEquiv
    (TrivSqZeroExt.kerIdeal K K) (dualNumberNilpotentIdeal_square K)

#print axioms kahlerSquareZeroLiftEquiv
#print axioms dualNumberNilpotentIdeal_square
#print axioms fst_constantDualNumberLift
#print axioms kahlerDualNumberLiftAtPoint

end Deligne21B

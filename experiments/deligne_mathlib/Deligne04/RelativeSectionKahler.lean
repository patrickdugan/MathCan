import Deligne04.OriginalPolynomialSchur
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.RingTheory.Ideal.Quotient.Over
import Mathlib.Tactic

/-!
# DEL-22F: relative Kähler presentation of the universal DEL-16 section quotient

Let P = K[a_i,c] and S = P[z_i] with the parameter variables
living in the coefficient ring. Retain the literal DEL-16 product
equations and adjoin the universal hyperplane section s as an
additional relation. The quotient T = S/(g_t,s) is an actual
P-algebra, including its redundant and nonreduced scheme structure.

Mathlib's Algebra.Presentation.differentials gives an exact
finite free presentation of Ω[T/P]. Its relation coefficients are
the original source-coordinate polynomial Jacobian entries mapped
into T. The coefficient parameters a_i,c are held constant by
the *relative* derivation.

This establishes an actual relative Kähler presentation, not an
intrinsic Fitting ideal. The determinantal/Fitting comparison and
constant-rank localization are separate follow-ups.
-/

open TensorProduct Module
open scoped BigOperators

namespace Deligne22F

/-- Actual universal parameter coefficient ring K[a_i,c]. -/
abbrev P (K : Type*) [Field K] (k s : ℕ) :=
  Deligne22B.ParameterRing K (Deligne16.Coord k s)

/-- The literal universal DEL-16 equations, with the section in the
none row and every original product equation in a some row. -/
noncomputable def universalRelation
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (t : Option (Deligne16.EqCoord k r)) :
    MvPolynomial (Deligne16.Coord k s) (P K k s) :=
  match t with
  | none => Deligne22B.universalSection B
  | some t =>
      MvPolynomial.map
        (MvPolynomial.C : K →+* P K k s)
        (Deligne16.copyEquation f t)

/-- Defining ideal of the genuine universal hyperplane section
scheme. No radicalization or loss of redundant equations. -/
noncomputable def universalSectionEquationsIdeal
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K) :
    Ideal (MvPolynomial (Deligne16.Coord k s) (P K k s)) :=
  Ideal.span (Set.range (universalRelation f B))

/-- Actual coordinate P-algebra T = P[z]/(g_t,s). -/
abbrev universalSectionQuotient
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K) :=
  MvPolynomial (Deligne16.Coord k s) (P K k s) ⧸
    universalSectionEquationsIdeal f B

/-- Actual algebra presentation with source-coordinate generators and
all original rows plus the independent universal section relation. -/
noncomputable def relativeSectionAlgebraPresentation
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K) :
    Algebra.Presentation (P K k s)
      (universalSectionQuotient f B)
      (Deligne16.Coord k s) (Option (Deligne16.EqCoord k r)) := by
  classical
  let I : Ideal (MvPolynomial (Deligne16.Coord k s) (P K k s)) :=
    universalSectionEquationsIdeal f B
  let Q : MvPolynomial (Deligne16.Coord k s) (P K k s) →ₐ[P K k s]
      universalSectionQuotient f B :=
    Ideal.Quotient.mkₐ (P K k s) I
  have hQ : Function.Surjective Q := fun x =>
    Ideal.Quotient.mk_surjective x
  let G : Algebra.Generators (P K k s) (universalSectionQuotient f B)
      (Deligne16.Coord k s) := Algebra.Generators.ofAlgHom Q hQ
  refine {
    toGenerators := G
    relation := universalRelation f B
    span_range_relation_eq_ker := ?_ }
  change I = G.ker
  rw [show G.ker = RingHom.ker Q.toRingHom from
    Algebra.Generators.ker_ofAlgHom Q hQ]
  exact (Ideal.mk_ker).symm

/-- The real Kähler differential module of T relative to P,
presented using the *literal original equations plus the section*. -/
noncomputable def relativeSectionKahlerPresentation
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K) :
    Module.Presentation (universalSectionQuotient f B)
      Ω[universalSectionQuotient f B⁄P K k s] :=
  (relativeSectionAlgebraPresentation f B).differentials

/-- The genuinely presented Kähler module has source-coordinate
generators and exactly the original rows with one added section row. -/
theorem relativeSectionKahler_indices
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K) :
    (relativeSectionKahlerPresentation f B).G = Deligne16.Coord k s ∧
    (relativeSectionKahlerPresentation f B).R =
      Option (Deligne16.EqCoord k r) := by
  exact ⟨rfl, rfl⟩

/-- The universal relation derivatives are exactly the rows of the
DEL-22B actual augmented Jacobian, with parameters constant. -/
theorem universalRelation_pderiv
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (t : Option (Deligne16.EqCoord k r))
    (i : Deligne16.Coord k s) :
    MvPolynomial.pderiv i (universalRelation f B t) =
      Deligne22B.universalAugmentedMatrix f B t i := by
  cases t with
  | none => rfl
  | some t =>
      exact MvPolynomial.pderiv_map
        (φ := MvPolynomial.C : K →+* P K k s)
        (f := Deligne16.copyEquation f t)
        (i := i)

/-- Any actual algebra presentation over a commutative base ring
presents its Kähler-relation coefficients by formal partial derivatives.
This is the general relative-base analogue of DEL-21F's field lemma. -/
theorem differential_relation_coefficient_relative
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι σ : Type*} (pres : Algebra.Presentation R S ι σ)
    (t : σ) (i : ι) :
    (pres.differentials).relation t i =
      algebraMap pres.Ring S (MvPolynomial.pderiv i (pres.relation t)) := by
  classical
  change (Finsupp.mapRange (algebraMap pres.Ring S) (by simp)
    ((KaehlerDifferential.mvPolynomialBasis R ι).repr
      (KaehlerDifferential.D R pres.Ring (pres.relation t)))) i =
        algebraMap pres.Ring S (MvPolynomial.pderiv i (pres.relation t))
  simp only [Finsupp.mapRange_apply,
    KaehlerDifferential.mvPolynomialBasis_repr_apply]

/-- Every coefficient in the *actual* relative Kähler presentation
is the corresponding universal augmented-Jacobian entry in T,
with exactly the DEL-16 relation list and its section row. -/
theorem relativeSectionKahler_relation_eq_universalJacobian
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (t : Option (Deligne16.EqCoord k r))
    (i : Deligne16.Coord k s) :
    (relativeSectionKahlerPresentation f B).relation t i =
      algebraMap
        (MvPolynomial (Deligne16.Coord k s) (P K k s))
        (universalSectionQuotient f B)
        (Deligne22B.universalAugmentedMatrix f B t i) := by
  rw [relativeSectionKahlerPresentation]
  rw [differential_relation_coefficient_relative]
  congr 1
  exact universalRelation_pderiv f B t i

/-- Mathlib's true differential presentation is exact for the
universal quotient, retaining the complete original ideal. -/
theorem relativeSectionKahler_exact
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K) :
    Function.Exact
      (relativeSectionKahlerPresentation f B).toRelations.map
      (relativeSectionKahlerPresentation f B).toSolution.π :=
  (relativeSectionKahlerPresentation f B).exact

#print axioms relativeSectionKahler_indices
#print axioms universalRelation_pderiv
#print axioms differential_relation_coefficient_relative
#print axioms relativeSectionKahler_relation_eq_universalJacobian
#print axioms relativeSectionKahler_exact

end Deligne22F

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

set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

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

/-- A finite family of polynomial equations over *any* commutative
coefficient ring presents its literal ideal quotient as an algebra.
Abstracting the coefficient ring keeps the nested K[a,c][z] algebra
instance out of the construction of the generic proof. -/
noncomputable def finiteRelationsAlgebraPresentation
    {R : Type*} [CommRing R] {ι σ : Type*}
    (rel : σ → MvPolynomial ι R) :
    Algebra.Presentation R
      (MvPolynomial ι R ⧸ Ideal.span (Set.range rel)) ι σ := by
  classical
  let I : Ideal (MvPolynomial ι R) := Ideal.span (Set.range rel)
  let Q : MvPolynomial ι R →ₐ[R] (MvPolynomial ι R ⧸ I) :=
    Ideal.Quotient.mkₐ R I
  have hQ : Function.Surjective Q :=
    fun x => Ideal.Quotient.mk_surjective x
  let G : Algebra.Generators R (MvPolynomial ι R ⧸ I) ι :=
    Algebra.Generators.ofAlgHom Q hQ
  refine {
    toGenerators := G
    relation := rel
    span_range_relation_eq_ker := ?_ }
  change I = G.ker
  rw [show G.ker = RingHom.ker Q.toRingHom from
    Algebra.Generators.ker_ofAlgHom Q hQ]
  exact (Ideal.mk_ker).symm

/-- The actual universal section quotient algebra over K[a_i,c],
using the generic finite-relations presentation on the complete
original equations and the additional universal section. -/
noncomputable def relativeSectionAlgebraPresentation
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K) :=
  finiteRelationsAlgebraPresentation (universalRelation f B)

/-- Mathlib's authentic finite presentation of the Kähler module
of the universal section quotient relative to K[a_i,c]. -/
noncomputable def relativeSectionKahlerPresentation
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K) :=
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
        (φ := (MvPolynomial.C : K →+* P K k s))
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

/-- Every relation coefficient in the genuine Kähler module is the
universal augmented-Jacobian entry under the *actual presentation*
algebra map to the section quotient. The subsequent identification
of that map with the canonical ideal-quotient map is a separate
naturality lemma. -/
theorem relativeSectionKahler_relation_eq_universalJacobian
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (t : Option (Deligne16.EqCoord k r))
    (i : Deligne16.Coord k s) :
    (relativeSectionKahlerPresentation f B).relation t i =
      algebraMap (relativeSectionAlgebraPresentation f B).Ring
        (universalSectionQuotient f B)
        (Deligne22B.universalAugmentedMatrix f B t i) := by
  change ((relativeSectionAlgebraPresentation f B).differentials).relation t i = _
  rw [differential_relation_coefficient_relative]
  have hr :
      (relativeSectionAlgebraPresentation f B).relation t =
        universalRelation f B t := rfl
  rw [hr, universalRelation_pderiv f B t i]

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

import Deligne04.ActualQuotientKahler
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic

/-!
# DEL-21F: the pointwise fiber of the genuine Kaehler module

Work on the actual coordinate algebra A = K[z]/I introduced in DEL-21E.
First construct the K-valued quotient-algebra point from the original
lifted polynomial equations, then tensor the genuine Kaehler presentation
along that point. Tensoring is right-exact, including when K is not flat
as an A-module. The remaining coordinate computation identifies the image
of the tensorized relation map with DEL-21D's Jacobian-row span.
-/

open TensorProduct Module

namespace Deligne21F

/-- An on-scheme K-point produces a K-algebra homomorphism from the
true full-ideal coordinate ring to K. -/
noncomputable def productPoint
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u) :
    Deligne21E.productCoordinateRing (k := k) f →ₐ[K] K := by
  apply Ideal.Quotient.liftₐ (Deligne16.productIdeal f) (MvPolynomial.aeval u)
  intro P hP
  have hI : Deligne16.productIdeal f ≤
      RingHom.ker (MvPolynomial.aeval u).toRingHom := by
    rw [Deligne16.productIdeal, Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    exact RingHom.mem_ker.mpr (by simpa using hu t)
  exact RingHom.mem_ker.mp (hI hP)

/-- The quotient point agrees with evaluation on every polynomial,
not only on the chosen generators. -/
theorem productPoint_mk
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u)
    (P : MvPolynomial (Deligne16.Coord k s) K) :
    productPoint f u hu (Ideal.Quotient.mk (Deligne16.productIdeal f) P) =
      MvPolynomial.eval u P := by
  simp [productPoint]

/-- The actual Kaehler presentation remains exact after
specializing along any K-rational point of A. This uses right exactness,
not flatness of the point's residue field over A. -/
theorem productKahler_fiber_right_exact
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (point : Deligne21E.productCoordinateRing (k := k) f →ₐ[K] K) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) K :=
      point.toRingHom.toAlgebra
    Function.Exact
      ((Deligne21E.productKahlerPresentation (k := k) f).toRelations.map.lTensor K)
      ((Deligne21E.productKahlerPresentation (k := k) f).toSolution.π.lTensor K) := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) K :=
    point.toRingHom.toAlgebra
  exact lTensor_exact K
    (Deligne21E.productKahlerPresentation (k := k) f).exact
    (Deligne21E.productKahlerPresentation (k := k) f).surjective_π

/-- Every coefficient in the actual Mathlib Kähler presentation is
the image of the genuine formal partial derivative of its original
polynomial relation. This holds before base change and for nonreduced
or redundant relations as well. -/
theorem differential_relation_coefficient
    {K : Type*} [Field K] {S : Type*} [CommRing S] [Algebra K S]
    {ι σ : Type*} (pres : Algebra.Presentation K S ι σ)
    (t : σ) (i : ι) :
    (pres.differentials).relation t i =
      algebraMap pres.Ring S (MvPolynomial.pderiv i (pres.relation t)) := by
  classical
  change (Finsupp.mapRange (algebraMap pres.Ring S) (by simp)
    ((KaehlerDifferential.mvPolynomialBasis K ι).repr
      (KaehlerDifferential.D K pres.Ring (pres.relation t)))) i =
        algebraMap pres.Ring S (MvPolynomial.pderiv i (pres.relation t))
  simp only [Finsupp.mapRange_apply,
    KaehlerDifferential.mvPolynomialBasis_repr_apply]

/-- At an arbitrary K-valued point, genuine Kähler presentation
coefficients evaluate to the original polynomial Jacobian entries,
in the coordinates supplied by the algebra presentation. -/
theorem differential_relation_coefficient_at_point
    {K : Type*} [Field K] {S : Type*} [CommRing S] [Algebra K S]
    {ι σ : Type*} (pres : Algebra.Presentation K S ι σ)
    (point : S →ₐ[K] K) (t : σ) (i : ι) :
    point ((pres.differentials).relation t i) =
      MvPolynomial.eval (fun j : ι => point (pres.val j))
        (MvPolynomial.pderiv i (pres.relation t)) := by
  rw [differential_relation_coefficient]
  rw [pres.toGenerators.algebraMap_apply]
  rw [MvPolynomial.comp_aeval_apply]
  rfl

/-- The actual quotient point takes every coordinate residue class
to its assigned value. -/
theorem productPoint_val
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u)
    (j : Deligne16.Coord k s) :
    productPoint f u hu
      ((Deligne21E.productAlgebraPresentation (k := k) f).val j) = u j := by
  change productPoint f u hu
    (Ideal.Quotient.mk (Deligne16.productIdeal f) (MvPolynomial.X j)) = u j
  simpa using productPoint_mk f u hu (MvPolynomial.X j)

/-- For the DEL-16 embedded product, the genuine Kähler relations
specialize to exactly DEL-21D's original evaluated Jacobian rows. -/
theorem productKahler_relation_at_point
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u)
    (t : Deligne16.EqCoord k r) (i : Deligne16.Coord k s) :
    productPoint f u hu
      ((Deligne21E.productKahlerPresentation (k := k) f).relation t i) =
        Deligne21D.conormalRow f u t i := by
  have h := differential_relation_coefficient_at_point
    (Deligne21E.productAlgebraPresentation (k := k) f)
    (productPoint f u hu) t i
  have hval : (fun j : Deligne16.Coord k s =>
      productPoint f u hu
        ((Deligne21E.productAlgebraPresentation (k := k) f).val j)) = u := by
    funext j
    exact productPoint_val f u hu j
  rw [hval] at h
  have hr :
      (Deligne21E.productAlgebraPresentation (k := k) f).relation t =
        Deligne16.copyEquation f t := rfl
  rw [hr] at h
  change productPoint f u hu
    (((Deligne21E.productAlgebraPresentation (k := k) f).differentials).relation t i) =
      MvPolynomial.eval u (MvPolynomial.pderiv i (Deligne16.copyEquation f t))
  exact h

/-- The canonical base-change coordinate isomorphism for a finite free
module at a K-valued algebra point. The A-algebra structure on K
is explicitly induced by the point. -/
noncomputable def coordinateTensorEquiv
    {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]
    {ι : Type*} [Fintype ι] (point : A →ₐ[K] K) :
    letI : Algebra A K := point.toRingHom.toAlgebra
    (K ⊗[A] (ι →₀ A)) ≃ₗ[K] (ι → K) := by
  letI : Algebra A K := point.toRingHom.toAlgebra
  classical
  exact ((Finsupp.basisSingleOne : Basis ι A (ι →₀ A)).baseChange K).repr.trans
    (Finsupp.linearEquivFunOnFinite K K ι)

/-- Each coordinate after tensoring along a point evaluates the old
coefficient at that point. -/
theorem coordinateTensorEquiv_one_tmul
    {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]
    {ι : Type*} [Fintype ι] (point : A →ₐ[K] K)
    (v : ι →₀ A) (i : ι) :
    letI : Algebra A K := point.toRingHom.toAlgebra
    coordinateTensorEquiv (ι := ι) point (1 ⊗ₜ[A] v) i = point (v i) := by
  letI : Algebra A K := point.toRingHom.toAlgebra
  classical
  simp only [coordinateTensorEquiv, LinearEquiv.trans_apply,
    Finsupp.linearEquivFunOnFinite_apply, Basis.baseChange_repr_tmul]
  change (v i) • (1 : K) = point (v i)
  simp only [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
  rfl

/-- Basis vectors of the specialized free module are the actual
coordinate unit vectors at the chosen K-valued point. -/
theorem coordinateTensorEquiv_single
    {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (point : A →ₐ[K] K)
    (t : ι) :
    letI : Algebra A K := point.toRingHom.toAlgebra
    coordinateTensorEquiv (ι := ι) point
      (1 ⊗ₜ[A] (Finsupp.single t (1 : A))) =
        (Pi.single t (1 : K) : ι → K) := by
  letI : Algebra A K := point.toRingHom.toAlgebra
  classical
  ext i
  rw [coordinateTensorEquiv_one_tmul]
  by_cases hi : i = t
  · subst i
    simp
  · simp [Pi.single_apply, Finsupp.single_apply, hi, Ne.symm hi]

/-- The span of Mathlib's genuine Kähler module-presentation
relations, evaluated at the actual quotient point, is exactly
DEL-21D's polynomial Jacobian-row conormal span. -/
theorem productKahler_evaluated_relation_span
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u) :
    Submodule.span K
      (Set.range (fun t : Deligne16.EqCoord k r =>
        (fun i : Deligne16.Coord k s =>
          productPoint f u hu
            ((Deligne21E.productKahlerPresentation (k := k) f).relation t i)))) =
      Deligne21D.conormalRelations f u := by
  let rows : Deligne16.EqCoord k r → Deligne16.Coord k s → K :=
    fun t i => productPoint f u hu
      ((Deligne21E.productKahlerPresentation (k := k) f).relation t i)
  have hrows : rows = Deligne21D.conormalRow f u := by
    funext t i
    exact productKahler_relation_at_point f u hu t i
  change Submodule.span K (Set.range rows) =
    Submodule.span K (Set.range (Deligne21D.conormalRow f u))
  rw [hrows]

/-- Base-changing the genuine Kähler presentation's relation
map and expressing it in the finite coordinate bases gives precisely
the K-linear map with DEL-21D's evaluated Jacobian rows. -/
theorem productKahler_relation_map_baseChange
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) K :=
      (productPoint f u hu).toRingHom.toAlgebra
    (coordinateTensorEquiv (ι := Deligne16.Coord k s)
        (productPoint f u hu)).toLinearMap.comp
      ((Deligne21E.productKahlerPresentation (k := k) f).toRelations.map.baseChange K) =
    (Fintype.linearCombination K (Deligne21D.conormalRow f u)).comp
      (coordinateTensorEquiv (ι := Deligne16.EqCoord k r)
        (productPoint f u hu)).toLinearMap := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) K :=
    (productPoint f u hu).toRingHom.toAlgebra
  classical
  apply ((Finsupp.basisSingleOne :
      Basis (Deligne16.EqCoord k r) (Deligne21E.productCoordinateRing (k := k) f)
        (Deligne16.EqCoord k r →₀ Deligne21E.productCoordinateRing (k := k) f)
      ).baseChange K).ext
  intro t
  ext i
  simp only [Basis.baseChange_apply, Finsupp.coe_basisSingleOne]
  conv_lhs =>
    change coordinateTensorEquiv (ι := Deligne16.Coord k s) (productPoint f u hu)
      (((Deligne21E.productKahlerPresentation (k := k) f).toRelations.map.baseChange K)
        (1 ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f]
          (Finsupp.single t 1))) i
  conv_rhs =>
    change (Fintype.linearCombination K (Deligne21D.conormalRow f u))
      (coordinateTensorEquiv (ι := Deligne16.EqCoord k r) (productPoint f u hu)
        (1 ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f]
          (Finsupp.single t 1))) i
  rw [LinearMap.baseChange_tmul, Module.Relations.map_single,
    coordinateTensorEquiv_one_tmul, coordinateTensorEquiv_single,
    Fintype.linearCombination_apply_single, one_smul]
  exact productKahler_relation_at_point f u hu t i

#print axioms productPoint_mk
#print axioms productKahler_fiber_right_exact
#print axioms differential_relation_coefficient
#print axioms differential_relation_coefficient_at_point
#print axioms productPoint_val
#print axioms productKahler_relation_at_point
#print axioms coordinateTensorEquiv_one_tmul
#print axioms coordinateTensorEquiv_single
#print axioms productKahler_evaluated_relation_span
#print axioms productKahler_relation_map_baseChange

end Deligne21F

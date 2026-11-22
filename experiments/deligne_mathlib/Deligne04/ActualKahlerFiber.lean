import Deligne04.ActualQuotientKahler
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Free
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

#print axioms productPoint_mk
#print axioms productKahler_fiber_right_exact
#print axioms differential_relation_coefficient
#print axioms differential_relation_coefficient_at_point
#print axioms productPoint_val

end Deligne21F

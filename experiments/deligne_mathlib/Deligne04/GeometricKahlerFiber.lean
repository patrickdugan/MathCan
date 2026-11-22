import Deligne04.ActualKahlerFiber
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic

/-!
# DEL-21G: geometric points of the actual quotient coordinate algebra

DEL-21F gives a genuine Kaehler cotangent-fiber equivalence at K-points.
Here we first construct the K-algebra point from an arbitrary extension
field L/K and carry the original Kähler module presentation through
tensoring with L along that point.

The original DEL-16 defining ideal, with nilpotents and redundant
relations, remains unchanged. Later DEL-21G lemmas will identify the
L-vector-space cokernel with the evaluated Jacobian-row quotient.
-/

open TensorProduct Module

namespace Deligne21G

/-- A geometric point over an arbitrary field extension of K that
vanishes on every original DEL-16 lifted equation of U^k. -/
def onGeometricProduct
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L) : Prop :=
  ∀ t : Deligne16.EqCoord k r,
    MvPolynomial.aeval u (Deligne16.copyEquation f t) = 0

/-- Every polynomial in the original full ideal vanishes at a
geometric point, including polynomial multiples and nilpotent relations. -/
private theorem geometricPoint_vanishes
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : onGeometricProduct f u) :
    ∀ P : MvPolynomial (Deligne16.Coord k s) K,
      P ∈ Deligne16.productIdeal f → MvPolynomial.aeval u P = 0 := by
  intro P hP
  have hI : Deligne16.productIdeal f ≤
      RingHom.ker (MvPolynomial.aeval u).toRingHom := by
    rw [Deligne16.productIdeal, Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    exact RingHom.mem_ker.mpr (hu t)
  exact RingHom.mem_ker.mp (hI hP)

/-- The original quotient A=K[z]/I evaluated at an L-valued point.
This uses the complete ideal, including nonreduced equations. -/
noncomputable def productGeometricPoint
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : onGeometricProduct f u) :
    Deligne21E.productCoordinateRing (k := k) f →ₐ[K] L :=
  Ideal.Quotient.liftₐ (Deligne16.productIdeal f) (MvPolynomial.aeval u)
    (geometricPoint_vanishes f u hu)

/-- Every class of an original polynomial evaluates by aeval at
the geometric point, retaining all scheme relations. -/
theorem productGeometricPoint_mk
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : onGeometricProduct f u)
    (P : MvPolynomial (Deligne16.Coord k s) K) :
    productGeometricPoint f u hu
      (Ideal.Quotient.mk (Deligne16.productIdeal f) P) =
        MvPolynomial.aeval u P := by
  have hc := Ideal.Quotient.liftₐ_comp (Deligne16.productIdeal f)
    (MvPolynomial.aeval u) (geometricPoint_vanishes f u hu)
  have hp := congrArg
    (fun φ : MvPolynomial (Deligne16.Coord k s) K →ₐ[K] L => φ P) hc
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    productGeometricPoint] using hp

/-- The actual coordinate residues specialize to their assigned
L-values at a geometric point. -/
theorem productGeometricPoint_val
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : onGeometricProduct f u)
    (j : Deligne16.Coord k s) :
    productGeometricPoint f u hu
      ((Deligne21E.productAlgebraPresentation (k := k) f).val j) = u j := by
  change productGeometricPoint f u hu
    (Ideal.Quotient.mk (Deligne16.productIdeal f) (MvPolynomial.X j)) = u j
  simpa using productGeometricPoint_mk f u hu (MvPolynomial.X j)

/-- Specializing the true Kähler presentation along A→L preserves
its cokernel sequence, even when L is not flat over A. -/
theorem productGeometricKahler_right_exact
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (point : Deligne21E.productCoordinateRing (k := k) f →ₐ[K] L) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      point.toRingHom.toAlgebra
    Function.Exact
      ((Deligne21E.productKahlerPresentation (k := k) f).toRelations.map.lTensor L)
      ((Deligne21E.productKahlerPresentation (k := k) f).toSolution.π.lTensor L) := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    point.toRingHom.toAlgebra
  exact lTensor_exact L
    (Deligne21E.productKahlerPresentation (k := k) f).exact
    (Deligne21E.productKahlerPresentation (k := k) f).surjective_π

/-- Geometric-point evaluation of Mathlib's actual Kähler relation
coefficients, with the original polynomial coefficients still in K. -/
theorem differential_relation_coefficient_at_geometric_point
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {S : Type*} [CommRing S] [Algebra K S]
    {ι σ : Type*} (pres : Algebra.Presentation K S ι σ)
    (point : S →ₐ[K] L) (t : σ) (i : ι) :
    point ((pres.differentials).relation t i) =
      MvPolynomial.aeval (fun j : ι => point (pres.val j))
        (MvPolynomial.pderiv i (pres.relation t)) := by
  rw [Deligne21F.differential_relation_coefficient]
  rw [pres.toGenerators.algebraMap_apply]
  rw [MvPolynomial.comp_aeval_apply]

/-- Original DEL-16 polynomial Jacobian row evaluated at an L-point,
with the original coefficients retained over K. -/
noncomputable def geometricConormalRow
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (t : Deligne16.EqCoord k r) : Deligne16.Coord k s → L :=
  fun i => MvPolynomial.aeval u
    (MvPolynomial.pderiv i (Deligne16.copyEquation f t))

noncomputable def geometricConormalRelations
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L) :
    Subspace L (Deligne16.Coord k s → L) :=
  Submodule.span L (Set.range (geometricConormalRow f u))

abbrev geometricCotangentFiber
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L) :=
  (Deligne16.Coord k s → L) ⧸ geometricConormalRelations f u

/-- The true quotient algebra's Kähler presentation evaluates to the
original (K-coefficient) Jacobian row at an L-valued geometric point. -/
theorem geometricKahler_relation_at_point
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : onGeometricProduct f u)
    (t : Deligne16.EqCoord k r) (i : Deligne16.Coord k s) :
    productGeometricPoint f u hu
      ((Deligne21E.productKahlerPresentation (k := k) f).relation t i) =
        geometricConormalRow f u t i := by
  have h := differential_relation_coefficient_at_geometric_point
    (Deligne21E.productAlgebraPresentation (k := k) f)
    (productGeometricPoint f u hu) t i
  have hval : (fun j : Deligne16.Coord k s =>
      productGeometricPoint f u hu
        ((Deligne21E.productAlgebraPresentation (k := k) f).val j)) = u := by
    funext j
    exact productGeometricPoint_val f u hu j
  rw [hval] at h
  have hr :
      (Deligne21E.productAlgebraPresentation (k := k) f).relation t =
        Deligne16.copyEquation f t := rfl
  rw [hr] at h
  change productGeometricPoint f u hu
    (((Deligne21E.productAlgebraPresentation (k := k) f).differentials).relation t i) =
      MvPolynomial.aeval u (MvPolynomial.pderiv i (Deligne16.copyEquation f t))
  exact h

/-- The finite free coordinates of a module over the genuine quotient
A, after extension to L through any K-algebra point A→L. -/
noncomputable def geometricCoordinateTensorEquiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A : Type*} [CommRing A] [Algebra K A]
    {ι : Type*} [Fintype ι] (point : A →ₐ[K] L) :
    letI : Algebra A L := point.toRingHom.toAlgebra
    (L ⊗[A] (ι →₀ A)) ≃ₗ[L] (ι → L) := by
  letI : Algebra A L := point.toRingHom.toAlgebra
  classical
  exact ((Finsupp.basisSingleOne : Basis ι A (ι →₀ A)).baseChange L).repr.trans
    (Finsupp.linearEquivFunOnFinite L L ι)

/-- Coordinates of a pure fiber tensor are the geometric-point
evaluations of its original A-valued coordinate coefficients. -/
theorem geometricCoordinateTensorEquiv_one_tmul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A : Type*} [CommRing A] [Algebra K A]
    {ι : Type*} [Fintype ι] (point : A →ₐ[K] L)
    (v : ι →₀ A) (i : ι) :
    letI : Algebra A L := point.toRingHom.toAlgebra
    geometricCoordinateTensorEquiv (ι := ι) point (1 ⊗ₜ[A] v) i = point (v i) := by
  letI : Algebra A L := point.toRingHom.toAlgebra
  classical
  simp only [geometricCoordinateTensorEquiv, LinearEquiv.trans_apply,
    Finsupp.linearEquivFunOnFinite_apply, Basis.baseChange_repr_tmul]
  change (v i) • (1 : L) = point (v i)
  simp only [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
  rfl

/-- A finite free basis vector becomes the actual L-coordinate
unit vector, over arbitrary extension fields. -/
theorem geometricCoordinateTensorEquiv_single
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A : Type*} [CommRing A] [Algebra K A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (point : A →ₐ[K] L)
    (t : ι) :
    letI : Algebra A L := point.toRingHom.toAlgebra
    geometricCoordinateTensorEquiv (ι := ι) point
      (1 ⊗ₜ[A] (Finsupp.single t (1 : A))) =
        (Pi.single t (1 : L) : ι → L) := by
  letI : Algebra A L := point.toRingHom.toAlgebra
  classical
  ext i
  rw [geometricCoordinateTensorEquiv_one_tmul]
  by_cases hi : i = t
  · subst i
    simp
  · simp [Pi.single_apply, Finsupp.single_apply, hi, Ne.symm hi]

/-- Evaluating genuine Kähler relations at an L-point gives the
full original Jacobian row span over L. -/
theorem geometricKahler_evaluated_relation_span
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : onGeometricProduct f u) :
    Submodule.span L
      (Set.range (fun t : Deligne16.EqCoord k r =>
        (fun i : Deligne16.Coord k s =>
          productGeometricPoint f u hu
            ((Deligne21E.productKahlerPresentation (k := k) f).relation t i)))) =
      geometricConormalRelations f u := by
  let rows : Deligne16.EqCoord k r → Deligne16.Coord k s → L :=
    fun t i => productGeometricPoint f u hu
      ((Deligne21E.productKahlerPresentation (k := k) f).relation t i)
  have hrows : rows = geometricConormalRow f u := by
    funext t i
    exact geometricKahler_relation_at_point f u hu t i
  change Submodule.span L (Set.range rows) =
    Submodule.span L (Set.range (geometricConormalRow f u))
  rw [hrows]

#print axioms productGeometricPoint_mk
#print axioms productGeometricPoint_val
#print axioms productGeometricKahler_right_exact
#print axioms differential_relation_coefficient_at_geometric_point
#print axioms geometricKahler_relation_at_point
#print axioms geometricCoordinateTensorEquiv_one_tmul
#print axioms geometricCoordinateTensorEquiv_single
#print axioms geometricKahler_evaluated_relation_span

end Deligne21G

import Deligne04.ActualKahlerFiber
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
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

#print axioms productGeometricPoint_mk
#print axioms productGeometricPoint_val
#print axioms productGeometricKahler_right_exact

end Deligne21G

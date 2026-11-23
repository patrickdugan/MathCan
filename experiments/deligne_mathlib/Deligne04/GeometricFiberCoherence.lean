import Deligne04.GeometricFiberNaturality
import Mathlib.Tactic

/-!
# DEL-21I: coordinate coherence for the geometric cotangent-tangent duality

The first refinement identifies the coordinate of DEL-21G's quotient-dual
equivalence directly with evaluation on the original coordinate class.
The quotient and Jacobian tangent remain those of the complete DEL-16
defining ideal, with nilpotent and redundant equations retained.
-/

open TensorProduct Module

namespace Deligne21I

/-- A functional on the actual geometric conormal quotient corresponds to
the original Jacobian tangent vector whose i-th coordinate is its value
on the class of the i-th coordinate basis vector. -/
theorem geometricCotangentDualEquivTangent_coord
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (ψ : Module.Dual L (Deligne21G.geometricCotangentFiber f u))
    (i : Deligne16.Coord k s) :
    ((Deligne21G.geometricCotangentDualEquivTangent f u ψ :
        Deligne21G.geometricJacobianTangent f u) :
        Deligne16.Coord k s → L) i =
      ψ (Submodule.Quotient.mk (Pi.single i (1 : L))) := by
  classical
  change ((Deligne21G.geometricConormalRelations f u).dualQuotEquivDualAnnihilator ψ :
      Module.Dual L (Deligne16.Coord k s → L))
      (Pi.single i (1 : L)) =
        ψ (Submodule.Quotient.mk (Pi.single i (1 : L)))
  exact Submodule.dualQuotEquivDualAnnihilator_apply _ _ _

#print axioms geometricCotangentDualEquivTangent_coord

/-- The dual-defined field-extension tangent equivalence sends the pure
tensor of an original Jacobian tangent vector to its coordinatewise
image under the field algebra homomorphism. -/
theorem geometricJacobianTangentTowerEquiv_one_tmul
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : Deligne21G.onGeometricProduct f u)
    (φ : L →ₐ[K] M)
    (v : Deligne21G.geometricJacobianTangent f u) :
    letI : Algebra L M := φ.toRingHom.toAlgebra
    (Deligne21H.geometricJacobianTangentTowerEquiv f u hu φ)
      ((1 : M) ⊗ₜ[L] v) =
      ⟨fun i => φ ((v : Deligne16.Coord k s → L) i),
        Deligne21H.geometricJacobianTangent_map_mem f u
          (v : Deligne16.Coord k s → L) φ v.property⟩ := by
  letI : Algebra L M := φ.toRingHom.toAlgebra
  classical
  let eQ := Deligne21H.geometricCotangentTowerEquiv f u hu φ
  let j : Deligne21G.geometricCotangentFiber f u →ₗ[L]
      Deligne21G.geometricCotangentFiber f (fun i => φ (u i)) :=
    (eQ.toLinearMap.restrictScalars L).comp
      (TensorProduct.mk L M (Deligne21G.geometricCotangentFiber f u) 1)
  have hb : IsBaseChange M j :=
    IsBaseChange.of_equiv eQ (by intro x; rfl)
  let eL := Deligne21G.geometricCotangentDualEquivTangent f u
  let eM := Deligne21G.geometricCotangentDualEquivTangent f (fun i => φ (u i))
  have hcoord (i : Deligne16.Coord k s) :
      (eL.symm v) (Submodule.Quotient.mk (Pi.single i (1 : L))) =
        (v : Deligne16.Coord k s → L) i := by
    have h := geometricCotangentDualEquivTangent_coord f u (eL.symm v) i
    simpa only [eL, LinearEquiv.apply_symm_apply] using h.symm
  have hsingle (i : Deligne16.Coord k s) :
      j (Submodule.Quotient.mk (Pi.single i (1 : L))) =
        Submodule.Quotient.mk (Pi.single i (1 : M)) := by
    exact Deligne21H.geometricCotangentTowerEquiv_single f u hu φ i
  have hdual (i : Deligne16.Coord k s) :
      (hb.toDualBaseChange ((1 : M) ⊗ₜ[L] (eL.symm v)))
        (Submodule.Quotient.mk (Pi.single i (1 : M))) =
          φ ((v : Deligne16.Coord k s → L) i) := by
    rw [← hsingle i]
    rw [IsBaseChange.toDualBaseChange_tmul]
    simp only [one_mul]
    change φ ((eL.symm v)
        (Submodule.Quotient.mk (Pi.single i (1 : L)))) =
          φ ((v : Deligne16.Coord k s → L) i)
    exact congrArg φ (hcoord i)
  have htrans :
      Deligne21H.geometricJacobianTangentTowerEquiv f u hu φ
        ((1 : M) ⊗ₜ[L] v) =
          eM (hb.toDualBaseChange ((1 : M) ⊗ₜ[L] (eL.symm v))) := by
    change ((eL.symm.baseChange L M _ _).trans (hb.toDualBaseChange.trans eM))
      ((1 : M) ⊗ₜ[L] v) = _
    simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  apply Subtype.ext
  funext i
  rw [htrans]
  change ((eM (hb.toDualBaseChange ((1 : M) ⊗ₜ[L] (eL.symm v))) :
      Deligne21G.geometricJacobianTangent f (fun i => φ (u i))) :
        Deligne16.Coord k s → M) i =
          φ ((v : Deligne16.Coord k s → L) i)
  rw [geometricCotangentDualEquivTangent_coord]
  exact hdual i

#print axioms geometricJacobianTangentTowerEquiv_one_tmul

/-- The original DEL-16 K-valued scheme point is a geometric point
after specializing the extension field to K itself. -/
theorem onGeometricProduct_self
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u) :
    Deligne21G.onGeometricProduct f u := by
  intro t
  simpa only [MvPolynomial.aeval_eq_eval] using hu t

/-- The two point constructions for the full DEL-16 quotient algebra
are the same algebra map at a base-field point. -/
theorem productGeometricPoint_self
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u) :
    Deligne21G.productGeometricPoint f u (onGeometricProduct_self f u hu) =
      Deligne21F.productPoint f u hu := by
  apply AlgHom.ext
  intro q
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Deligne21G.productGeometricPoint_mk, Deligne21F.productPoint_mk]
  rfl

/-- The two Kähler fiber equivalences agree on each original quotient
coordinate class, using the full scheme ideal and its original rows. -/
theorem geometricKahlerSelfEquiv_mk
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u v : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) K :=
      (Deligne21F.productPoint f u hu).toRingHom.toAlgebra
    ((Deligne21H.geometricCotangentSelfEquiv f u).trans
      (Deligne21F.productKahlerFiberEquiv f u hu))
        (Submodule.Quotient.mk v) =
      (Deligne21G.geometricKahlerFiberEquiv f u
        (onGeometricProduct_self f u hu))
        (Submodule.Quotient.mk v) := by
  rfl

/-- Over the base field, DEL-21F's and DEL-21G's original-ideal
quotient-to-Kähler fiber isomorphisms are the same entire linear map. -/
theorem geometricKahlerSelfEquiv
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → K)
    (hu : Deligne16.onEmbeddedProduct f u) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) K :=
      (Deligne21F.productPoint f u hu).toRingHom.toAlgebra
    (Deligne21H.geometricCotangentSelfEquiv f u).trans
      (Deligne21F.productKahlerFiberEquiv f u hu) =
    Deligne21G.geometricKahlerFiberEquiv f u
      (onGeometricProduct_self f u hu) := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) K :=
    (Deligne21F.productPoint f u hu).toRingHom.toAlgebra
  apply LinearEquiv.ext
  intro q
  obtain ⟨v, rfl⟩ :=
    Submodule.Quotient.mk_surjective (Deligne21G.geometricConormalRelations f u) q
  exact geometricKahlerSelfEquiv_mk f u v hu

#print axioms onGeometricProduct_self
#print axioms productGeometricPoint_self
#print axioms geometricKahlerSelfEquiv_mk
#print axioms geometricKahlerSelfEquiv

end Deligne21I

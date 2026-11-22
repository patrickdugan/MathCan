import Deligne04.ActualKahlerFiber
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic

open scoped BigOperators

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

/-- Tensoring the true quotient-ring Kähler relation map to L and
converting its finite free coordinates gives the linear combination
of the original K-coefficient polynomial Jacobian rows over L. -/
theorem geometricKahler_relation_map_baseChange
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : onGeometricProduct f u) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      (productGeometricPoint f u hu).toRingHom.toAlgebra
    (geometricCoordinateTensorEquiv (ι := Deligne16.Coord k s)
        (productGeometricPoint f u hu)).toLinearMap.comp
      ((Deligne21E.productKahlerPresentation (k := k) f).toRelations.map.baseChange L) =
    (Fintype.linearCombination L (geometricConormalRow f u)).comp
      (geometricCoordinateTensorEquiv (ι := Deligne16.EqCoord k r)
        (productGeometricPoint f u hu)).toLinearMap := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (productGeometricPoint f u hu).toRingHom.toAlgebra
  classical
  apply ((Finsupp.basisSingleOne :
      Basis (Deligne16.EqCoord k r) (Deligne21E.productCoordinateRing (k := k) f)
        (Deligne16.EqCoord k r →₀ Deligne21E.productCoordinateRing (k := k) f)
      ).baseChange L).ext
  intro t
  ext i
  simp only [Basis.baseChange_apply, Finsupp.coe_basisSingleOne]
  conv_lhs =>
    change geometricCoordinateTensorEquiv (ι := Deligne16.Coord k s)
      (productGeometricPoint f u hu)
      (((Deligne21E.productKahlerPresentation (k := k) f).toRelations.map.baseChange L)
        (1 ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f]
          (Finsupp.single t 1))) i
  conv_rhs =>
    change (Fintype.linearCombination L (geometricConormalRow f u))
      (geometricCoordinateTensorEquiv (ι := Deligne16.EqCoord k r)
        (productGeometricPoint f u hu)
        (1 ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f]
          (Finsupp.single t 1))) i
  rw [LinearMap.baseChange_tmul]
  have hrel :
      (Deligne21E.productKahlerPresentation (k := k) f).toRelations.map
        (Finsupp.single t 1) =
      (Deligne21E.productKahlerPresentation (k := k) f).relation t :=
    (Deligne21E.productKahlerPresentation (k := k) f).toRelations.map_single t
  rw [hrel]
  have hl :
      geometricCoordinateTensorEquiv (ι := Deligne16.Coord k s)
        (productGeometricPoint f u hu)
        (1 ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f]
          (Deligne21E.productKahlerPresentation (k := k) f).relation t) i =
      productGeometricPoint f u hu
        ((Deligne21E.productKahlerPresentation (k := k) f).relation t i) :=
    geometricCoordinateTensorEquiv_one_tmul
      (ι := Deligne16.Coord k s) (productGeometricPoint f u hu)
      ((Deligne21E.productKahlerPresentation (k := k) f).relation t) i
  have hr :
      (Fintype.linearCombination L (geometricConormalRow f u))
        (geometricCoordinateTensorEquiv (ι := Deligne16.EqCoord k r)
          (productGeometricPoint f u hu)
          (1 ⊗ₜ[Deligne21E.productCoordinateRing (k := k) f]
            (Finsupp.single t 1))) i = geometricConormalRow f u t i := by
    rw [geometricCoordinateTensorEquiv_single (ι := Deligne16.EqCoord k r)
        (productGeometricPoint f u hu) t,
      Fintype.linearCombination_apply_single, one_smul]
  exact hl.trans ((geometricKahler_relation_at_point f u hu t i).trans hr.symm)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The image of the entire base-changed true Kähler relation map,
in finite geometric coordinates, equals the L-span of original
Jacobian rows, including their nonreduced and redundant relations. -/
theorem geometricKahler_relation_range_baseChange
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : onGeometricProduct f u) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      (productGeometricPoint f u hu).toRingHom.toAlgebra
    (LinearMap.range
        ((Deligne21E.productKahlerPresentation (k := k) f).toRelations.map.baseChange L)).map
      (geometricCoordinateTensorEquiv (ι := Deligne16.Coord k s)
        (productGeometricPoint f u hu)).toLinearMap =
      geometricConormalRelations f u := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (productGeometricPoint f u hu).toRingHom.toAlgebra
  classical
  rw [← LinearMap.range_comp]
  rw [geometricKahler_relation_map_baseChange f u hu]
  rw [LinearEquiv.range_comp]
  simpa only [geometricConormalRelations] using
    (Fintype.range_linearCombination L (geometricConormalRow f u))

/-- Right exactness over the field extension identifies the kernel
of the L-linear Kähler fiber surjection with the image of its
actual base-changed relation map. -/
theorem geometricKahler_fiber_kernel
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (point : Deligne21E.productCoordinateRing (k := k) f →ₐ[K] L) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      point.toRingHom.toAlgebra
    LinearMap.ker
      ((Deligne21E.productKahlerPresentation (k := k) f).toSolution.π.baseChange L) =
    LinearMap.range
      ((Deligne21E.productKahlerPresentation (k := k) f).toRelations.map.baseChange L) := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    point.toRingHom.toAlgebra
  have he : Function.Exact
      ((Deligne21E.productKahlerPresentation (k := k) f).toRelations.map.baseChange L)
      ((Deligne21E.productKahlerPresentation (k := k) f).toSolution.π.baseChange L) := by
    simpa only [LinearMap.baseChange_eq_lTensor] using
      (productGeometricKahler_right_exact f point)
  exact LinearMap.exact_iff.mp he

/-- The genuine relative Kähler differential fiber at any
extension-valued geometric point is the L-vector-space quotient
by the actual original defining-polynomial Jacobian rows. -/
noncomputable def geometricKahlerFiberEquiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : onGeometricProduct f u) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      (productGeometricPoint f u hu).toRingHom.toAlgebra
    geometricCotangentFiber f u ≃ₗ[L]
      L ⊗[Deligne21E.productCoordinateRing (k := k) f]
        Ω[Deligne21E.productCoordinateRing (k := k) f⁄K] := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (productGeometricPoint f u hu).toRingHom.toAlgebra
  let e := geometricCoordinateTensorEquiv (ι := Deligne16.Coord k s)
    (productGeometricPoint f u hu)
  let rel := (Deligne21E.productKahlerPresentation (k := k) f).toRelations.map.baseChange L
  let π := (Deligne21E.productKahlerPresentation (k := k) f).toSolution.π.baseChange L
  let g : (Deligne16.Coord k s → L) →ₗ[L]
      (L ⊗[Deligne21E.productCoordinateRing (k := k) f]
        Ω[Deligne21E.productCoordinateRing (k := k) f⁄K]) :=
    π.comp e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    LinearMap.baseChange_surjective L
      (Deligne21E.productKahlerPresentation (k := k) f).surjective_π
  have hg : Function.Surjective g := hπ.comp e.symm.surjective
  have hexact : LinearMap.ker π = LinearMap.range rel :=
    geometricKahler_fiber_kernel f (productGeometricPoint f u hu)
  have hrange : (LinearMap.range rel).map e.toLinearMap =
      geometricConormalRelations f u :=
    geometricKahler_relation_range_baseChange f u hu
  have hker : LinearMap.ker g = geometricConormalRelations f u := by
    ext v
    change π (e.symm v) = 0 ↔ v ∈ geometricConormalRelations f u
    rw [← LinearMap.mem_ker, hexact]
    constructor
    · intro hv
      have hm : v ∈ (LinearMap.range rel).map e.toLinearMap :=
        ⟨e.symm v, hv, e.apply_symm_apply v⟩
      rwa [hrange] at hm
    · intro hv
      have hm : v ∈ (LinearMap.range rel).map e.toLinearMap := by
        rw [hrange]
        exact hv
      obtain ⟨w, hw, heq⟩ := hm
      have he : e.symm v = w := by
        calc
          e.symm v = e.symm (e w) := congrArg e.symm heq.symm
          _ = w := e.symm_apply_apply w
      rw [he]
      exact hw
  exact (Submodule.quotEquivOfEq
      (geometricConormalRelations f u) (LinearMap.ker g) hker.symm).trans
    (g.quotKerEquivOfSurjective hg)

/-- The geometric polynomial Jacobian tangent, represented as
vectors in L^(ks), is the annihilator of the genuine conormal
relations in finite coordinate duality. -/
noncomputable def geometricJacobianTangent
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L) :
    Subspace L (Deligne16.Coord k s → L) :=
  (geometricConormalRelations f u).dualAnnihilator.comap
    ((LinearEquiv.piRing L L (Deligne16.Coord k s) L).symm.toLinearMap)

/-- In geometric coordinates, tangent membership is exactly the
equation that every *original* polynomial Jacobian row annihilates v. -/
theorem mem_geometricJacobianTangent_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u v : Deligne16.Coord k s → L) :
    v ∈ geometricJacobianTangent f u ↔
      ∀ t : Deligne16.EqCoord k r,
        (∑ i : Deligne16.Coord k s, geometricConormalRow f u t i * v i) = 0 := by
  classical
  change ((LinearEquiv.piRing L L (Deligne16.Coord k s) L).symm v :
    Module.Dual L (Deligne16.Coord k s → L)) ∈
      (geometricConormalRelations f u).dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h t
    have hrow : geometricConormalRow f u t ∈ geometricConormalRelations f u :=
      Submodule.subset_span (Set.mem_range_self t)
    have hz := h (geometricConormalRow f u t) hrow
    simpa only [LinearEquiv.piRing_symm_apply, smul_eq_mul] using hz
  · intro hv
    have hker : geometricConormalRelations f u ≤
        LinearMap.ker
          ((LinearEquiv.piRing L L (Deligne16.Coord k s) L).symm v) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨t, rfl⟩
      change ((LinearEquiv.piRing L L (Deligne16.Coord k s) L).symm v)
        (geometricConormalRow f u t) = 0
      simpa only [LinearEquiv.piRing_symm_apply, smul_eq_mul] using hv t
    intro w hw
    exact hker hw

/-- The dual of the original-Jacobian quotient equals the
geometric tangent subspace of L^(ks). -/
noncomputable def geometricCotangentDualEquivTangent
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L) :
    Module.Dual L (geometricCotangentFiber f u) ≃ₗ[L]
      geometricJacobianTangent f u := by
  classical
  let E := LinearEquiv.piRing L L (Deligne16.Coord k s) L
  have he :
      (geometricConormalRelations f u).dualAnnihilator =
        (geometricJacobianTangent f u).comap E.toLinearMap := by
    ext phi
    change phi ∈ (geometricConormalRelations f u).dualAnnihilator ↔
      E phi ∈ (geometricConormalRelations f u).dualAnnihilator.comap E.symm.toLinearMap
    change phi ∈ (geometricConormalRelations f u).dualAnnihilator ↔
      E.symm (E phi) ∈ (geometricConormalRelations f u).dualAnnihilator
    rw [E.symm_apply_apply]
  exact ((geometricConormalRelations f u).dualQuotEquivDualAnnihilator).trans
    ((LinearEquiv.ofEq _ _ he).trans
      (E.ofSubmodule' (geometricJacobianTangent f u)))

/-- The true Kähler cotangent-fiber dual over an arbitrary field
extension L/K is exactly the original Jacobian-kernel tangent
space at the L-valued point. -/
noncomputable def geometricKahlerFiberDualEquivTangent
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (u : Deligne16.Coord k s → L)
    (hu : onGeometricProduct f u) :
    letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
      (productGeometricPoint f u hu).toRingHom.toAlgebra
    Module.Dual L
      (L ⊗[Deligne21E.productCoordinateRing (k := k) f]
        Ω[Deligne21E.productCoordinateRing (k := k) f⁄K]) ≃ₗ[L]
      geometricJacobianTangent f u := by
  letI : Algebra (Deligne21E.productCoordinateRing (k := k) f) L :=
    (productGeometricPoint f u hu).toRingHom.toAlgebra
  exact (geometricKahlerFiberEquiv f u hu).dualMap.trans
    (geometricCotangentDualEquivTangent f u)

#print axioms productGeometricPoint_mk
#print axioms productGeometricPoint_val
#print axioms productGeometricKahler_right_exact
#print axioms differential_relation_coefficient_at_geometric_point
#print axioms geometricKahler_relation_at_point
#print axioms geometricCoordinateTensorEquiv_one_tmul
#print axioms geometricCoordinateTensorEquiv_single
#print axioms geometricKahler_evaluated_relation_span
#print axioms geometricKahler_relation_map_baseChange
#print axioms geometricKahler_relation_range_baseChange
#print axioms geometricKahler_fiber_kernel
#print axioms geometricKahlerFiberEquiv
#print axioms mem_geometricJacobianTangent_iff
#print axioms geometricCotangentDualEquivTangent
#print axioms geometricKahlerFiberDualEquivTangent

end Deligne21G

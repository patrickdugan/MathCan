import Deligne04.RelativeCriticalMinors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# DEL-22B: universal relative critical incidence with genuine parameter variables

The parameter coefficients of the hyperplane section live in
P = K[a_i,c], and its source coordinates live in P[z_i].
The parameter ring is not specialized until the explicit map
P → K is applied. Differentiation uses pderiv in the source
coordinates only. Original DEL-16 equations and their nilpotent
and redundant relations are retained verbatim.
-/

open TensorProduct Module
open scoped BigOperators

namespace Deligne22B

/-- The polynomial ring in all linear coefficients and the constant:
some i denotes a_i, none denotes c. -/
abbrev ParameterRing (K : Type*) [CommSemiring K] (ι : Type*) := MvPolynomial (Option ι) K

/-- Specialize the independent parameters to (a,c) over the coefficient field. -/
noncomputable def parameterEval
    {K : Type*} [Field K] {ι : Type*}
    (a : ι → K) (c : K) : ParameterRing K ι →+* K :=
  (MvPolynomial.aeval (fun j : Option ι => j.elim c a)).toRingHom

@[simp]
theorem parameterEval_C
    {K : Type*} [Field K] {ι : Type*}
    (a : ι → K) (c x : K) :
    parameterEval a c (MvPolynomial.C x : ParameterRing K ι) = x := by
  simp [parameterEval]

@[simp]
theorem parameterEval_X_some
    {K : Type*} [Field K] {ι : Type*}
    (a : ι → K) (c : K) (i : ι) :
    parameterEval a c (MvPolynomial.X (some i) : ParameterRing K ι) = a i := by
  simp [parameterEval]

@[simp]
theorem parameterEval_X_none
    {K : Type*} [Field K] {ι : Type*}
    (a : ι → K) (c : K) :
    parameterEval a c (MvPolynomial.X none : ParameterRing K ι) = c := by
  simp [parameterEval]

/-- Coefficient extension along K → K[a,c], followed by parameter
evaluation, is the identity on the *entire* original polynomial ring. -/
theorem map_C_specialize
    {K : Type*} [Field K] {ι : Type*}
    (a : ι → K) (c : K) (p : MvPolynomial ι K) :
    MvPolynomial.map (parameterEval a c)
      (MvPolynomial.map
        (MvPolynomial.C : K →+* ParameterRing K ι) p) = p := by
  rw [MvPolynomial.map_map]
  have h :
      (parameterEval a c).comp
        (MvPolynomial.C : K →+* ParameterRing K ι) = RingHom.id K := by
    ext x
    simp
  rw [h, MvPolynomial.map_id]

/-- A family of actual DEL-16 fixed-last-coefficient sections
over the independent parameter polynomial ring K[a_i,c]. -/
noncomputable def universalSection
    {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (B : MvPolynomial ι K) :
    MvPolynomial ι (ParameterRing K ι) :=
  MvPolynomial.map
      (MvPolynomial.C : K →+* ParameterRing K ι) B +
    (∑ i : ι,
      MvPolynomial.C
        (MvPolynomial.X (some i) : ParameterRing K ι) *
        MvPolynomial.X i) +
    MvPolynomial.C (MvPolynomial.X none : ParameterRing K ι)

/-- Every actual fixed-parameter section is the coefficient
specialization of the one universal polynomial section. -/
theorem universalSection_specialize
    {K : Type*} [Field K]
    {ι : Type*} [Fintype ι]
    (B : MvPolynomial ι K) (a : ι → K) (c : K) :
    MvPolynomial.map (parameterEval a c) (universalSection B) =
      B + (∑ i : ι, MvPolynomial.C (a i) * MvPolynomial.X i) +
        MvPolynomial.C c := by
  classical
  simp [universalSection, map_C_specialize]

/-- Specializing a universal partial derivative in z_i recovers the
actual derivative of the fixed-parameter original polynomial section. -/
theorem universalSection_pderiv_specialize
    {K : Type*} [Field K]
    {ι : Type*} [Fintype ι]
    (B : MvPolynomial ι K) (a : ι → K) (c : K) (i : ι) :
    MvPolynomial.map (parameterEval a c)
      (MvPolynomial.pderiv i (universalSection B)) =
    MvPolynomial.pderiv i
      (B + (∑ j : ι, MvPolynomial.C (a j) * MvPolynomial.X j) +
         MvPolynomial.C c) := by
  rw [← MvPolynomial.pderiv_map, universalSection_specialize]

/-- Universal full-ideal augmented Jacobian: parameter variables
are coefficients and receive no z-partial differentiation. -/
noncomputable def universalAugmentedMatrix
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K) :
    Matrix (Option (Deligne16.EqCoord k r)) (Deligne16.Coord k s)
      (MvPolynomial (Deligne16.Coord k s)
        (ParameterRing K (Deligne16.Coord k s))) :=
  fun t i => match t with
    | none => MvPolynomial.pderiv i (universalSection B)
    | some t => MvPolynomial.map
        (MvPolynomial.C : K →+* ParameterRing K (Deligne16.Coord k s))
        (MvPolynomial.pderiv i (Deligne16.copyEquation f t))

/-- Universal Jacobian coefficient specialization equals DEL-22A's
original fixed-parameter polynomial augmented Jacobian in every entry. -/
theorem universalAugmentedMatrix_specialize
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K) :
    (universalAugmentedMatrix f B).map
      (MvPolynomial.map (parameterEval a c)) =
      Deligne22A.polynomialAugmentedSectionMatrix f B a c := by
  classical
  ext t i : 1
  cases t with
  | none =>
      change MvPolynomial.map (parameterEval a c)
        (MvPolynomial.pderiv i (universalSection B)) =
        MvPolynomial.pderiv i (Deligne16.fixedSection B a c)
      rw [← MvPolynomial.pderiv_map]
      simpa only [Deligne16.fixedSection] using
        congrArg (MvPolynomial.pderiv i)
          (universalSection_specialize B a c)
  | some t =>
      exact map_C_specialize a c
        (MvPolynomial.pderiv i (Deligne16.copyEquation f t))

/-- Size-(d+1) minors, now polynomials in source coordinates
with *independent* a_i,c parameter coefficients. -/
noncomputable def universalMinor
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (d : ℕ)
    (rr : Fin (d+1) → Option (Deligne16.EqCoord k r))
    (cc : Fin (d+1) → Deligne16.Coord k s) :
    MvPolynomial (Deligne16.Coord k s)
      (ParameterRing K (Deligne16.Coord k s)) :=
  ((universalAugmentedMatrix f B).submatrix rr cc).det

/-- The specialization of every universal original-Jacobian minor
equals DEL-22A's fixed-parameter minor exactly. -/
theorem universalMinor_specialize
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K) (d : ℕ)
    (rr : Fin (d+1) → Option (Deligne16.EqCoord k r))
    (cc : Fin (d+1) → Deligne16.Coord k s) :
    MvPolynomial.map (parameterEval a c)
      (universalMinor f B d rr cc) =
      Deligne22A.augmentedMinorPolynomial f B a c d rr cc := by
  change (MvPolynomial.map (parameterEval a c))
    (((universalAugmentedMatrix f B).submatrix rr cc).det) =
    ((Deligne22A.polynomialAugmentedSectionMatrix f B a c).submatrix rr cc).det
  rw [RingHom.map_det]
  congr 1
  ext i j : 1
  have h := universalAugmentedMatrix_specialize f B a c
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply] using
    congrArg
      (fun A : Matrix (Option (Deligne16.EqCoord k r))
        (Deligne16.Coord k s) (MvPolynomial (Deligne16.Coord k s) K) =>
        A (rr i) (cc j)) h

/-- The genuine universal determinantal ideal in K[a_i,c][z_i],
before any section-parameter specialization or Zariski projection. -/
noncomputable def universalMinorIdeal
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K) (d : ℕ) :
    Ideal (MvPolynomial (Deligne16.Coord k s)
      (ParameterRing K (Deligne16.Coord k s))) :=
  Ideal.span (Set.range
    (fun rc : (Fin (d+1) → Option (Deligne16.EqCoord k r)) ×
        (Fin (d+1) → Deligne16.Coord k s) =>
      universalMinor f B d rc.1 rc.2))

#print axioms map_C_specialize
#print axioms universalSection_specialize
#print axioms universalSection_pderiv_specialize
#print axioms universalAugmentedMatrix_specialize
#print axioms universalMinor_specialize

end Deligne22B

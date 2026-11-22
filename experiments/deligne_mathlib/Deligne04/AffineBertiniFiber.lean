import Deligne04.EmbeddedProductIncidence
import Mathlib.Tactic

/-!
# DEL-19: affine parameter surjectivity at every embedded smooth point

Suppose a smooth affine V=U^k of dimension D has embedding
coordinates z_i, i in Fin M. At a geometric point v, their actual
cotangent vectors dz_i span T_v*V because the coordinate map is
a closed immersion.

Write this cotangent-spanning condition as the explicit assumption
that every covector w : Fin D -> K is a linear combination of the
embedding-coordinate differentials dz_i.

For the fixed-coefficient section B+sum a_i z_i + c, the affine
parameter map
    (a,c) |-> (sum a_i dz_i, sum a_i z_i(v)+c)
is surjective onto (T_v*V) x K. The c variable independently
controls the section value, while the embedding coordinates
control the differential. This holds over fields of every
characteristic and for arbitrary fixed phase B.

Consequently the critical-parameter incidence at v is an affine
fiber of codimension D+1 in an M+1 dimensional parameter space.

This file kernel-certifies the augmented map's surjectivity and
the arithmetic codimension identity. The geometric step proving
the cotangent spanning assumption from the actual closed
immersion, and the scheme-theoretic dimension/projection
argument that extracts a nonzero Bertini polynomial for general
U^k, remain separate proof obligations.
-/

open scoped BigOperators

namespace Deligne19

/-- The cotangent component of a hyperplane perturbation, written
in coordinates of the D-dimensional tangent space. -/
def parameterDifferential
    {K : Type*} [CommRing K] {M D : ℕ}
    (dz : Fin M → Fin D → K)
    (a : Fin M → K) : Fin D → K :=
  fun j => ∑ i : Fin M, a i * dz i j

/-- The scalar value component, independently adjustable by c. -/
def parameterValue
    {K : Type*} [CommRing K] {M : ℕ}
    (z a : Fin M → K) (c : K) : K :=
  (∑ i : Fin M, a i * z i) + c

/-- Cotangent spanning gives surjectivity of the augmented affine
parameter map: the derivative directions are controlled by a_i,
and the free constant c independently sets the section value. -/
theorem exists_augmented_preimage
    {K : Type*} [Field K] {M D : ℕ}
    (dz : Fin M → Fin D → K) (z : Fin M → K)
    (hspan : ∀ w : Fin D → K,
      ∃ a : Fin M → K, ∀ j : Fin D,
        parameterDifferential dz a j = w j)
    (w : Fin D → K) (level : K) :
    ∃ a : Fin M → K, ∃ c : K,
      (∀ j : Fin D, parameterDifferential dz a j = w j) ∧
      parameterValue z a c = level := by
  obtain ⟨a, ha⟩ := hspan w
  refine ⟨a, level - (∑ i : Fin M, a i * z i), ha, ?_⟩
  simp only [parameterValue]
  ring

/-- The actual map from coefficient-and-constant parameters into
the product cotangent/value coordinate space is surjective. -/
theorem augmented_parameter_map_surjective
    {K : Type*} [Field K] {M D : ℕ}
    (dz : Fin M → Fin D → K) (z : Fin M → K)
    (hspan : ∀ w : Fin D → K,
      ∃ a : Fin M → K, ∀ j : Fin D,
        parameterDifferential dz a j = w j) :
    Function.Surjective
      (fun t : (Fin M → K) × K =>
        (parameterDifferential dz t.1, parameterValue z t.1 t.2)) := by
  intro target
  obtain ⟨a, c, ha, hv⟩ :=
    exists_augmented_preimage dz z hspan target.1 target.2
  refine ⟨(a, c), ?_⟩
  apply Prod.ext
  · funext j
    exact ha j
  · exact hv

/-- For ANY prescribed fixed path-phase B and its differential dB,
one can choose the variable affine hyperplane coefficients and
constant so that the section and all tangent derivatives vanish
at a given geometric point. The fixed coefficient of B is one. -/
theorem exists_fixed_phase_critical_parameter
    {K : Type*} [Field K] {M D : ℕ}
    (dz : Fin M → Fin D → K) (z : Fin M → K)
    (hspan : ∀ w : Fin D → K,
      ∃ a : Fin M → K, ∀ j : Fin D,
        parameterDifferential dz a j = w j)
    (B : K) (dB : Fin D → K) :
    ∃ a : Fin M → K, ∃ c : K,
      (∀ j : Fin D,
        dB j + parameterDifferential dz a j = 0) ∧
      B + parameterValue z a c = 0 := by
  obtain ⟨a, c, ha, hv⟩ :=
    exists_augmented_preimage dz z hspan
      (fun j => -(dB j)) (-B)
  refine ⟨a, c, ?_, ?_⟩
  · intro j
    rw [ha j]
    ring
  · rw [hv]
    ring

/-- Arithmetic of the affine critical-incidence fiber dimension:
an augmented rank of D+1 leaves M-D free parameter coordinates. -/
theorem affine_fiber_dimension_arithmetic
    (D M : ℕ) (hD : D ≤ M) :
    M + 1 - (D + 1) = M - D ∧
      (M - D) + D = M := by
  omega

/-- An embedded parameter space with M+1 coordinates has strictly
larger dimension than the predicted critical-incidence dimension M.
The geometric dimension theorem is still an explicit obligation. -/
theorem predicted_incidence_proper_arithmetic (M : ℕ) :
    M < M + 1 := by omega

#print axioms exists_augmented_preimage
#print axioms augmented_parameter_map_surjective
#print axioms exists_fixed_phase_critical_parameter
#print axioms affine_fiber_dimension_arithmetic
#print axioms predicted_incidence_proper_arithmetic

end Deligne19

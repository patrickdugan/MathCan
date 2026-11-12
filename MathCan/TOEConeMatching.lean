import MathCan.TOEFormSectors

/-!
# TOE-14: structural cone matching and Fourier phase identities

Kernel algebra for positive-weight two-cone models and the former TOE-13
Jordan-root lift. The expanded discriminant formula is independently checked
over exact rational coefficients by research/toe/cone_matching.py.

These lemmas do not formalize a source-normalized GfE action, its physical
constraints, an invariant tensor subsystem, or a hyperbolicity theorem.
-/
namespace MathCan.TOEConeMatching

/-- Two real cone centers, with polynomial amplitudes encoded as integers. -/
def conePolynomial (a b u v x : Int) : Int :=
  a * ((x-u)*(x-u)) + b * ((x-v)*(x-v))

/-- When the characteristic cones meet, their common center is a root. -/
theorem matched_cones_have_root (a b u : Int) :
    conePolynomial a b u u u = 0 := by
  simp [conePolynomial]

/-- At the first cone, the residual is exactly the other weighted gap. -/
theorem cone_gap_at_first_root (a b u v : Int) :
    conePolynomial a b u v u = b*((u-v)*(u-v)) := by
  simp [conePolynomial]

/-- Every nonzero weight detects a different cone center at the old root. -/
theorem mismatched_cones_lift_first_root (a b u v : Int)
    (hb : b ≠ 0) (huv : u ≠ v) :
    conePolynomial a b u v u ≠ 0 := by
  rw [cone_gap_at_first_root]
  have hd : u-v ≠ 0 := by omega
  intro hz
  rcases Int.mul_eq_zero.mp hz with hb0 | hsq
  · exact hb hb0
  · rcases Int.mul_eq_zero.mp hsq with hd0 | hd0
    · exact hd hd0
    · exact hd hd0

/-- Discriminant after the exact rational polynomial expansion.
This factored normalization is the object tested by the Python oracle. -/
def factoredDiscriminant (a b u v : Int) : Int :=
  (-4)*a*b*((u-v)*(u-v))

theorem matching_forces_zero_discriminant (a b u : Int) :
    factoredDiscriminant a b u u = 0 := by
  simp [factoredDiscriminant]

theorem mismatching_nonzero_discriminant (a b u v : Int)
    (ha : a ≠ 0) (hb : b ≠ 0) (huv : u ≠ v) :
    factoredDiscriminant a b u v ≠ 0 := by
  unfold factoredDiscriminant
  have hd : u-v ≠ 0 := by omega
  intro hz
  rcases Int.mul_eq_zero.mp hz with hleft | hright
  · rcases Int.mul_eq_zero.mp hleft with hleft | hbzero
    · rcases Int.mul_eq_zero.mp hleft with hconst | hazero
      · omega
      · exact ha hazero
    · exact hb hbzero
  · rcases Int.mul_eq_zero.mp hright with hd0 | hd0
    · exact hd hd0
    · exact hd hd0

/-- Exact Gaussian-integer multiplication: (a+ib)(c+id). -/
def gaussianMul (z w : Int × Int) : Int × Int :=
  (z.1*w.1-z.2*w.2, z.1*w.2+z.2*w.1)

/-- The upper/lower Fourier phase pair multiplies to the original b^2. -/
theorem phase_pair_product (b : Int) :
    gaussianMul (0,-b) (0,b) = (b*b,0) := by
  simp [gaussianMul, neg_mul]

/-- A two-mode unitary congruence preserves the formal determinant. -/
theorem phase_determinant_preserved (a b c : Int) :
    a*c - (gaussianMul (0,-b) (0,b)).1 = a*c - b*b := by
  simp [gaussianMul, neg_mul]

#print axioms matched_cones_have_root
#print axioms cone_gap_at_first_root
#print axioms mismatched_cones_lift_first_root
#print axioms matching_forces_zero_discriminant
#print axioms mismatching_nonzero_discriminant
#print axioms phase_pair_product
#print axioms phase_determinant_preserved

end MathCan.TOEConeMatching

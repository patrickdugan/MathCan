import Init

/-!
# SPC-03: algebraic anchors and affine recurrent increments

Theorems are exact over integers. This small Lean module checks the
algebra behind bias cancellation and contracting affine trajectories.
The complex-valued singular-value and Hankel-rank theorems in the
companion SPC-03 manuscript are written mathematical proofs, not
formalized by this Init-only specialization.
-/
namespace MathCan.ContractionAliasing

/-- A fixed anchor disappears from a difference observation. -/
theorem anchor_cancels (x y anchor : Int) :
    (x + anchor) - (y + anchor) = x - y := by
  omega

/-- Differences of a scalar affine recurrence are acted on by its linear part. -/
theorem affine_increment (a b x y : Int) :
    (a * x + b) - (a * y + b) = a * (x - y) := by
  simp only [Int.mul_sub]
  omega

/-- A two-point centered state and a constant anchor have exactly
separable squared energy. This is a minimal kernel-level DC-masking
identity; the full finite-dimensional Hilbert identity is in the note. -/
theorem paired_energy_split (anchor drift : Int) :
    (anchor + drift) * (anchor + drift) +
    (anchor - drift) * (anchor - drift) =
    2 * (anchor * anchor + drift * drift) := by
  simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
  omega

/-- Two equal one-step shifts have exactly equal increment energy. -/
theorem centered_two_step_increment (anchor x y : Int) :
    ((x + anchor) - (y + anchor)) * ((x + anchor) - (y + anchor)) =
      (x - y) * (x - y) := by
  simp only [anchor_cancels]

/-- Modulo 11 provides a finite nontrivial orbit check independent of
complex phases or floating-point error. -/
def affine11 (x : Nat) : Nat := (4 * x + 7) % 11

theorem affine11_distinguishes_adjacent_inputs :
    ∀ x y : Fin 11, affine11 x.val = affine11 y.val → x = y := by
  decide

#print axioms anchor_cancels
#print axioms affine_increment
#print axioms paired_energy_split
#print axioms centered_two_step_increment
#print axioms affine11_distinguishes_adjacent_inputs

end MathCan.ContractionAliasing

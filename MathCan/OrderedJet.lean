import Init

/-!
# OVC-01: finite ordered-probe kernel certificates

Companion to Compactification-Theory PR #133 using OpenAI #116/#135.
The general source theorems and probability/complexity claims are outside
this Init-only module. We check the algebraic numerator behind the
adjacent-swap Taylor coefficient and the explicit four-coordinate matrix
witness from the source #116 jet construction, scaled by denominator 24.
-/
namespace MathCan.OrderedJet

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Scalar substitutions commute and therefore miss a commutator. -/
theorem scalar_order_invisible (a b : Int) : a * b = b * a :=
  Int.mul_comm a b

/-- The weighted reciprocal-position difference, after multiplication
    by a common denominator a*b, has numerator b-a. -/
theorem adjacent_weighted_numerator (w a b : Int) :
    (w * b + (w - 1) * a) -
      (w * a + (w - 1) * b) = b - a := by
  simp only [Int.sub_mul, Int.one_mul]
  omega

/-- The source Taylor difference changes the sign of that numerator. -/
theorem adjacent_coefficient_numerator (w a b : Int) :
    -((w * b + (w - 1) * a) -
      (w * a + (w - 1) * b)) = a - b := by
  have h := adjacent_weighted_numerator w a b
  omega

theorem unequal_symbols_nonzero_numerator (a b : Int) (h : a ≠ b) :
    a - b ≠ 0 := by
  omega

/-- Twenty-four times the source T_1 on Taylor coordinates 0..3. -/
def jetOneScaled (r c : Fin 4) : Int :=
  match r.val, c.val with
  | 1, 0 => 24
  | 2, 0 => -12
  | 2, 1 => 12
  | 3, 0 => 8
  | 3, 1 => -8
  | 3, 2 => 8
  | _, _ => 0

/-- Twenty-four times T_2 on the same coordinates. -/
def jetTwoScaled (r c : Fin 4) : Int :=
  match r.val, c.val with
  | 1, 0 => 12
  | 2, 0 => -3
  | 2, 1 => 6
  | 3, 0 => 1
  | 3, 1 => -2
  | 3, 2 => 4
  | _, _ => 0

def productEntry (a b : Fin 4 → Fin 4 → Int) (r c : Fin 4) : Int :=
  ((List.finRange 4).map (fun k => a r k * b k c)).sum

def commutatorEntry (r c : Fin 4) : Int :=
  productEntry jetOneScaled jetTwoScaled r c -
    productEntry jetTwoScaled jetOneScaled r c

/-- Degrees 0,1,2 cannot see this order error; degree 3 sees -24.
    Divide by 24^2 to recover the rational witness -1/24. -/
theorem first_column_commutator_witness :
    commutatorEntry 0 0 = 0 ∧
    commutatorEntry 1 0 = 0 ∧
    commutatorEntry 2 0 = 0 ∧
    commutatorEntry 3 0 = -24 := by
  decide

theorem rational_witness_cross_multiplication :
    (-24 : Int) * 24 = (-1 : Int) * 24 ^ 2 := by
  decide

/-- The trace is zero although the preceding first column is nonzero. -/
theorem trace_misses_this_order_error :
    ((List.finRange 4).map (fun i => commutatorEntry i i)).sum = 0 := by
  decide

/-- The source-size dimensions used in two separately executed examples. -/
theorem checked_formula_dimensions :
    (2 : Nat) * 2 * 9 ^ 2 = 324 ∧
    (2 : Nat) * 3 * 13 ^ 2 = 1014 := by
  decide

#print axioms scalar_order_invisible
#print axioms adjacent_weighted_numerator
#print axioms adjacent_coefficient_numerator
#print axioms unequal_symbols_nonzero_numerator
#print axioms first_column_commutator_witness
#print axioms rational_witness_cross_multiplication
#print axioms trace_misses_this_order_error
#print axioms checked_formula_dimensions

end MathCan.OrderedJet

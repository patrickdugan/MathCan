import MathCan.CoalitionNoise

/-!
PEF-06T: pair-only class effects may come from thresholding additive logits.
The proof compares an additive score with a genuinely mixed AND score.
-/

namespace MathCan.CoalitionThreshold

def additiveLogit (x y : Int) : Int := x + y

/-- All four-corner differences of a separable additive score vanish. -/
theorem additive_four_corner_zero (x0 x1 y0 y1 : Int) :
    additiveLogit x1 y1 -
    additiveLogit x1 y0 -
    additiveLogit x0 y1 +
    additiveLogit x0 y0 = 0 := by
  simp only [additiveLogit]
  omega

def thresholdTwo (s : Nat) : Bool := decide (2 ≤ s)

/-- This class changes only when two bits flip, although its
    underlying logit is exactly additive. -/
theorem additive_threshold_pair_only :
    thresholdTwo (0+0) = false ∧
    thresholdTwo (1+0) = false ∧
    thresholdTwo (0+1) = false ∧
    thresholdTwo (1+1) = true := by
  decide

/-- The thresholded additive score has no mixed logit response. -/
theorem thresholded_pair_can_have_zero_second_difference :
    (2 : Int) - 1 - 1 + 0 = 0 ∧
    thresholdTwo 0 = thresholdTwo 1 ∧
    thresholdTwo 0 ≠ thresholdTwo 2 := by
  decide

def andLogit (x y : Int) : Int := x * y

/-- The nonlinear two-bit AND score has nonzero mixed difference. -/
theorem and_logit_has_mixed_difference :
    andLogit 1 1 - andLogit 1 0 -
    andLogit 0 1 + andLogit 0 0 = 1 := by
  decide

def thresholdOne (s : Nat) : Bool := decide (1 ≤ s)

theorem nonlinear_and_pair_only :
    thresholdOne (0*0) = false ∧
    thresholdOne (1*0) = false ∧
    thresholdOne (0*1) = false ∧
    thresholdOne (1*1) = true := by
  decide

#print axioms additive_four_corner_zero
#print axioms additive_threshold_pair_only
#print axioms thresholded_pair_can_have_zero_second_difference
#print axioms and_logit_has_mixed_difference
#print axioms nonlinear_and_pair_only

end MathCan.CoalitionThreshold

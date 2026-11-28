import Init

/-!
NRF-09: the arithmetic skeleton of matched-step depth comparisons.
The eight-arm median Lipschitz lemma and real quadratic risk bounds are
proved in the accompanying paper and tested with exact Fractions.
-/

namespace MathCan.MatchedStepMargin

/-- Equal-exposure contrast = equal-update depth contrast + update lag. -/
theorem depth_update_path (m16_u32 m32_u16 m32_u32 : Int) :
    m32_u16 - m16_u32 =
      (m32_u32 - m16_u32) + (m32_u16 - m32_u32) := by
  omega

/-- A positive signed margin survives a sufficiently small drift. -/
theorem positive_margin_stable
    (oldMargin newMargin bound : Int)
    (hbound : bound < oldMargin)
    (hmove : oldMargin - newMargin <= bound) :
    0 < newMargin := by
  omega

/-- A negative signed margin survives a sufficiently small drift. -/
theorem negative_margin_stable
    (oldMargin newMargin bound : Int)
    (hbound : oldMargin < -bound)
    (hmove : newMargin - oldMargin <= bound) :
    newMargin < 0 := by
  omega

#print axioms depth_update_path
#print axioms positive_margin_stable
#print axioms negative_margin_stable

end MathCan.MatchedStepMargin

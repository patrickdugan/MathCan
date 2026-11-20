import Init

/-!
# Cumulative adapter margins

Margins and loss budgets are integer-scaled exact quantities. Each certified
edge supplies an upper bound on its *actual* loss measured at the current
checkpoint, after previous adapters. A Taylor/Hessian certificate can supply
that edge bound; the proof here is independent of how it was obtained.
For rational values, multiply every margin and cap by a shared positive
denominator. The theorem does not certify the neural Hessian assumption.
-/

namespace SelfModels.ContinuityV1

/-- A path witnesses that each successor loses at most its declared budget.
    The budget is summed in chronological order. -/
inductive MarginPath : Int → Int → Int → Prop where
  | root (margin : Int) : MarginPath margin margin 0
  | extend {origin middle final priorBudget stepBudget : Int}
      (prior : MarginPath origin middle priorBudget)
      (hstep : middle ≤ final + stepBudget) :
      MarginPath origin final (priorBudget + stepBudget)

/-- Any finite succession has total loss at most the sum of its edge caps. -/
theorem marginPath_sound {origin final budget : Int}
    (path : MarginPath origin final budget) : origin ≤ final + budget := by
  induction path with
  | root margin => simp
  | @extend origin middle final priorBudget stepBudget prior hstep ih =>
    calc
      origin ≤ middle + priorBudget := ih
      _ ≤ (final + stepBudget) + priorBudget :=
        add_le_add_right hstep priorBudget
      _ = final + (priorBudget + stepBudget) := by
        simp [add_assoc, add_comm, add_left_comm]

/-- If the initial positive margin exceeds the total certified loss budget,
    the final margin must remain strictly positive. -/
theorem marginPath_preserves_positive {origin final budget : Int}
    (path : MarginPath origin final budget)
    (budgetBelowMargin : budget < origin) : 0 < final := by
  by_contra hnonpos
  have hfinal : final ≤ (0 : Int) := le_of_not_gt hnonpos
  have hbudget : final + budget ≤ budget := by
    simpa using add_le_add_right hfinal budget
  have hcontradiction : origin ≤ budget :=
    le_trans (marginPath_sound path) hbudget
  exact (not_le_of_gt budgetBelowMargin) hcontradiction

/-- The cross term can dominate two individually harmless adapter changes. -/
def interactionMargin (a b : Int) : Int := 1 - 4 * a * b

theorem individually_unchanged_and_jointly_reversed :
    interactionMargin 0 0 = 1 ∧
    interactionMargin 1 0 = 1 ∧
    interactionMargin 0 1 = 1 ∧
    interactionMargin 1 1 = -3 := by
  decide

/-- Its exact finite mixed difference is negative four. -/
theorem exact_mixed_difference :
    interactionMargin 1 1 - interactionMargin 1 0 -
      interactionMargin 0 1 + interactionMargin 0 0 = -4 := by
  decide

end SelfModels.ContinuityV1

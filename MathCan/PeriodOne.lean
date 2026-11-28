import Init

/-!
# NOR-05: the commutation-and-uniqueness core of period-one certification

For the trained GRU, F is its nonlinear one-step zero-input map,
G = F^12, B is a certified invariant Euclidean ball, and p is G's
unique fixed point in B. The exact interval certificate additionally
shows F(p) belongs to B. This Init-only module proves the general
logical implication independent of the analytic/norm parts.

This is a kernel-checked step in the full analytic theorem in
research/nor05/PERIOD_ONE_NONLINEAR_COMPACTIFICATION.md.
-/
namespace MathCan.PeriodOne

/-- If F and G commute at p, G has one fixed point p inside B,
and F maps p back into B, then F also fixes p. -/
theorem one_step_fixes_unique_block_point
    {α : Type} (F G : α → α) (B : α → Prop) (p : α)
    (hp : G p = p)
    (hcomm : G (F p) = F (G p))
    (hFpB : B (F p))
    (hunique : ∀ z, B z → G z = z → z = p) :
    F p = p := by
  have hG : G (F p) = F p := by
    simpa only [hp] using hcomm
  exact hunique (F p) hFpB hG

/-- Every F fixed point in B equals the unique G fixed point
whenever F fixed points are also G fixed points. -/
theorem one_step_fixed_point_unique
    {α : Type} (F G : α → α) (B : α → Prop) (p z : α)
    (huniqueG : ∀ x, B x → G x = x → x = p)
    (htransfer : F z = z → G z = z)
    (hzB : B z) (hzF : F z = z) : z = p := by
  exact huniqueG z hzB (htransfer hzF)

/-- A commutation and transfer certificate yields a unique one-step
fixed point inside the same block-invariant set. -/
theorem period_one_and_unique
    {α : Type} (F G : α → α) (B : α → Prop) (p : α)
    (hp : G p = p)
    (hcomm : G (F p) = F (G p))
    (hFpB : B (F p))
    (huniqueG : ∀ x, B x → G x = x → x = p)
    (htransfer : ∀ z, F z = z → G z = z) :
    F p = p ∧ ∀ z, B z → F z = z → z = p := by
  constructor
  · exact one_step_fixes_unique_block_point F G B p hp hcomm hFpB huniqueG
  · intro z hB hF
    exact one_step_fixed_point_unique F G B p z huniqueG (htransfer z) hB hF

#print axioms one_step_fixes_unique_block_point
#print axioms one_step_fixed_point_unique
#print axioms period_one_and_unique

end MathCan.PeriodOne

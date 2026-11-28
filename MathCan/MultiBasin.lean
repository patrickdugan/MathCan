import Init

/-!
# NOR-07: two-basin separation and terminal-code obstruction

This is the finite metric skeleton of multi-attractor history compression.
The original analytic construction is in research/nor07. We prove the
geometric lower bound for collapsing distinct basin anchors into a
single tail code and disjointness of certified balls, under explicit
symmetric triangle-inequality premises.

No external functional calculus, existence of two trained GRU fixed
points, or probabilistic finite Lp embedding theorem is axiomatized.
-/
namespace MathCan.MultiBasin

/-- Distinct closed balls cannot share a point when the sum of their
radii is strictly below the center distance. -/
theorem disjoint_balls
    {α : Type} (d : α → α → Nat)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (symmetric : ∀ x y, d x y = d y x)
    (p q : α) (r s : Nat)
    (sep : r + s < d p q) :
    ∀ x, d x p ≤ r → d x q ≤ s → False := by
  intro x hx hy
  have hp : d p x ≤ r := by
    rw [symmetric p x]
    exact hx
  have htri := triangle p x q
  omega

/-- When two late true states lie within radii of distinct attractor
centers, collapsing both to the same code entails an additive error
at least the center separation minus both radii. -/
theorem collapsed_terminal_code_cost
    {α : Type} (d : α → α → Nat)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (p q x y : α) (r s error : Nat)
    (hx : d p x ≤ r) (hy : d y q ≤ s)
    (hZeroCode : d x y ≤ error) :
    d p q ≤ r + s + error := by
  have ht1 := triangle p x y
  have ht2 := triangle p y q
  omega

/-- Algebraic version: a terminal-code channel with zero cross distance
cannot have additive error smaller than the inter-basin lower bound. -/
theorem collapsed_tail_error_lower
    (separation radiusLeft radiusRight err : Nat)
    (h : separation ≤ radiusLeft + radiusRight + err) :
    separation - (radiusLeft + radiusRight) ≤ err := by
  omega

/-- With two different terminal anchors, the clipped late-pair metric
may preserve the full anchor distance, provided endpoint errors fit
within a known bounded budget. -/
theorem distinct_anchors_stitch
    (anchorDistance realDistance leftError rightError : Nat)
    (hleft : realDistance ≤ anchorDistance + leftError + rightError)
    (hright : anchorDistance ≤ realDistance + leftError + rightError) :
    realDistance ≤ anchorDistance + (leftError + rightError) ∧
    anchorDistance ≤ realDistance + (leftError + rightError) := by
  constructor <;> omega

#print axioms disjoint_balls
#print axioms collapsed_terminal_code_cost
#print axioms collapsed_tail_error_lower
#print axioms distinct_anchors_stitch

end MathCan.MultiBasin

import Lean

namespace GalacticityRisk

/-- The least nonnegative cash reserve for a finite list of signed
    cumulative cash flows (over every compatible world and settlement). -/
def requiredReserve : List Int → Int
  | [] => 0
  | p :: ps =>
      if requiredReserve ps ≤ -p then -p else requiredReserve ps

theorem reserve_spec (ps : List Int) (K : Int) :
    requiredReserve ps ≤ K ↔
      0 ≤ K ∧ ∀ s, s ∈ ps → 0 ≤ K + s := by
  induction ps with
  | nil => simp [requiredReserve]
  | cons p ps ih =>
    have he : requiredReserve (p :: ps) ≤ K ↔
        (requiredReserve ps ≤ K ∧ -p ≤ K) := by
      simp only [requiredReserve]
      split <;> omega
    rw [he, ih]
    constructor
    · intro h
      obtain ⟨⟨hk, hs⟩, hp⟩ := h
      refine ⟨hk, ?_⟩
      intro s hm
      cases List.mem_cons.mp hm with
      | inl hEq =>
        subst s
        omega
      | inr hMem => exact hs s hMem
    · intro h
      obtain ⟨hk, hs⟩ := h
      refine ⟨⟨hk, ?_⟩, ?_⟩
      · intro s hm
        exact hs s (List.mem_cons.mpr (Or.inr hm))
      · have hp := hs p (by simp)
        omega

theorem reserve_nonnegative (ps : List Int) :
    0 ≤ requiredReserve ps := by
  have h : requiredReserve ps ≤ requiredReserve ps := by omega
  exact ((reserve_spec ps (requiredReserve ps)).mp h).1

theorem reserve_is_safe (ps : List Int) (s : Int) (h : s ∈ ps) :
    0 ≤ requiredReserve ps + s := by
  have hr : requiredReserve ps ≤ requiredReserve ps := by omega
  exact ((reserve_spec ps (requiredReserve ps)).mp hr).2 s h

/-- Restricting the compatible worlds or the list of possible prefixes
    cannot increase the required reserve. -/
theorem reserve_subset (xs ys : List Int)
    (incl : ∀ s, s ∈ xs → s ∈ ys) :
    requiredReserve xs ≤ requiredReserve ys := by
  apply (reserve_spec xs (requiredReserve ys)).mpr
  exact ⟨reserve_nonnegative ys, fun s h => reserve_is_safe ys s (incl s h)⟩

/-- If a settlement is paid, the remaining cash funds all later prefixes
    of that same compatible continuation. -/
theorem advance_reserve (K x : Int) (tail : List Int)
    (safe : requiredReserve (x :: tail.map (fun y => x + y)) ≤ K) :
    requiredReserve tail ≤ K + x := by
  have h := (reserve_spec (x :: tail.map (fun y => x + y)) K).mp safe
  apply (reserve_spec tail (K + x)).mpr
  refine ⟨h.2 x (by simp), ?_⟩
  intro s hs
  have hm : x + s ∈ tail.map (fun y => x + y) :=
    List.mem_map.mpr ⟨s, hs, rfl⟩
  have hcash := h.2 (x + s) (List.mem_cons.mpr (Or.inr hm))
  omega

/-- A reserve violation is a witness that at least one modeled prefix
    lacks enough cash (for a nonnegative current balance). -/
theorem reserve_violation (ps : List Int) (K : Int)
    (hk : 0 ≤ K) (bad : K < requiredReserve ps) :
    ¬ (∀ s, s ∈ ps → 0 ≤ K + s) := by
  intro safe
  have h := (reserve_spec ps K).mpr ⟨hk, safe⟩
  omega

/-- Buying is safe only when acquisition cost and the remaining
    liabilities can both be funded. -/
theorem purchase_reserve (cash cost reserve : Int)
    (hc : 0 ≤ cost) (hr : 0 ≤ reserve) :
    cost + reserve ≤ cash ↔ cost ≤ cash ∧ reserve ≤ cash - cost := by
  omega

/-- Pareto dominance is preserved by addition across disjoint observation
    branches, using unnormalized nonnegative integer world masses. -/
theorem branch_dominance (s₁ s₂ r₁ r₂ s r : Nat)
    (hs : s₁ ≤ s₂) (hr : r₂ ≤ r₁) :
    s₁ + s ≤ s₂ + s ∧ r₂ + r ≤ r₁ + r := by omega

theorem dominate_feasible (s₁ s₂ r₁ r₂ target budget : Nat)
    (hs : s₁ ≤ s₂) (hr : r₂ ≤ r₁)
    (ht : target ≤ s₁) (hb : r₁ ≤ budget) :
    target ≤ s₂ ∧ r₂ ≤ budget := by omega

end GalacticityRisk

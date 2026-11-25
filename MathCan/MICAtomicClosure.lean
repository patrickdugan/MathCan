import Init

namespace MathCan.MICAtomicClosure

abbrev Block (α : Type) := α → Prop

def Subset {α : Type} (A B : Block α) : Prop := ∀ i, A i → B i

def SupportMonotone {α : Type} (support : Block α → α → Prop) : Prop :=
  ∀ A B, Subset A B → ∀ i, support A i → support B i

def Feasible {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (S : Block α) : Prop :=
  ∀ i, S i → eligible i ∧ support S i

def peel {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (S : Block α) : Block α :=
  fun i => S i ∧ eligible i ∧ support S i

def passes {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (S : Block α) : Nat → Block α
  | 0 => S
  | k+1 => peel eligible support (passes eligible support S k)

/-- Every feasible subset survives a parallel deletion pass. -/
theorem preserve {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (mono : SupportMonotone support)
    (S B : Block α) (sub : Subset B S) (good : Feasible eligible support B) :
    Subset B (peel eligible support S) := by
  intro i hi
  exact ⟨sub i hi, (good i hi).1, mono B S sub i (good i hi).2⟩

theorem passes_preserve {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (mono : SupportMonotone support)
    (S B : Block α) (sub : Subset B S) (good : Feasible eligible support B)
    (k : Nat) : Subset B (passes eligible support S k) := by
  induction k with
  | zero => exact sub
  | succ k ih => exact preserve eligible support mono _ B ih good

theorem passes_subset {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (S : Block α) (k : Nat) :
    Subset (passes eligible support S k) S := by
  induction k with
  | zero => exact fun _ h => h
  | succ k ih =>
    intro i hi
    exact ih i hi.1

/-- A stable deletion pass is feasible and contains every feasible subset.
    Finite termination and sparse queue complexity are separate obligations. -/
theorem stable_greatest {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (mono : SupportMonotone support)
    (S : Block α) (k : Nat)
    (stable : Subset (passes eligible support S k)
      (peel eligible support (passes eligible support S k))) :
    Feasible eligible support (passes eligible support S k) ∧
    Subset (passes eligible support S k) S ∧
    (∀ B, Subset B S → Feasible eligible support B →
      Subset B (passes eligible support S k)) := by
  refine ⟨?_, passes_subset eligible support S k, ?_⟩
  · intro i hi
    exact (stable i hi).2
  · intro B sub good
    exact passes_preserve eligible support mono S B sub good k

/-- Construct the greatest feasible sub-block without a termination premise. -/
def greatest {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (S : Block α) : Block α :=
  fun i => ∃ B : Block α, Subset B S ∧ Feasible eligible support B ∧ B i

theorem greatest_feasible {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (mono : SupportMonotone support)
    (S : Block α) : Feasible eligible support (greatest eligible support S) := by
  intro i hi
  obtain ⟨B, sub, good, hBi⟩ := hi
  have hBG : Subset B (greatest eligible support S) := by
    intro j hj
    exact ⟨B, sub, good, hj⟩
  exact ⟨(good i hBi).1, mono B _ hBG i (good i hBi).2⟩

theorem greatest_subset {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (S : Block α) :
    Subset (greatest eligible support S) S := by
  intro i hi
  obtain ⟨B, sub, _, hBi⟩ := hi
  exact sub i hBi

theorem greatest_contains {α : Type} (eligible : α → Prop)
    (support : Block α → α → Prop) (S B : Block α)
    (sub : Subset B S) (good : Feasible eligible support B) :
    Subset B (greatest eligible support S) := by
  intro i hi
  exact ⟨B, sub, good, hi⟩

/-- One summand of the maximum-gap argument for nonnegative weights. -/
theorem weighted_gap_bound (a d D : Int) (ha : 0 ≤ a) (hd : d ≤ D) :
    d*a ≤ (D-1)*a + (if d = D then a else 0) := by
  by_cases he : d = D
  · subst d
    rw [if_pos rfl, Int.sub_mul, Int.one_mul]
    omega
  · have hdiff : 0 ≤ D-1-d := by omega
    have hprod := Int.mul_nonneg hdiff ha
    simp only [Int.sub_mul, Int.one_mul] at hprod
    simp only [if_neg he, Int.add_zero, Int.sub_mul, Int.one_mul]
    omega

def mass : List (Int × Int) → Int
  | [] => 0
  | x :: xs => x.1 + mass xs

def weightedGap : List (Int × Int) → Int
  | [] => 0
  | x :: xs => x.2*x.1 + weightedGap xs

def maxSupport (D : Int) : List (Int × Int) → Int
  | [] => 0
  | x :: xs => (if x.2 = D then x.1 else 0) + maxSupport D xs

/-- Rows contain (dependency coefficient, integer difference) pairs. -/
theorem row_gap_bound (D : Int) (xs : List (Int × Int))
    (h : ∀ x ∈ xs, 0 ≤ x.1 ∧ x.2 ≤ D) :
    weightedGap xs ≤ (D-1)*mass xs + maxSupport D xs := by
  induction xs with
  | nil => simp [weightedGap, mass, maxSupport]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    have hb := weighted_gap_bound x.1 x.2 D hx.1 hx.2
    simp only [weightedGap, mass, maxSupport, Int.mul_add]
    omega

/-- For a maximal positive gap D, a feasible smaller certificate implies
    the unit-decrement support inequality at every maximum-gap coordinate.
    hgap is the difference of the two certificate inequalities for the row. -/
theorem unit_threshold_of_gap (D slack : Int) (xs : List (Int × Int))
    (hD : 1 ≤ D) (hmass : mass xs ≤ 10)
    (h : ∀ x ∈ xs, 0 ≤ x.1 ∧ x.2 ≤ D)
    (hgap : 10*D ≤ slack + weightedGap xs) :
    10 ≤ slack + maxSupport D xs := by
  have hb := row_gap_bound D xs h
  have hnon : 0 ≤ (D-1)*(10-mass xs) :=
    Int.mul_nonneg (by omega) (by omega)
  simp only [Int.mul_sub, Int.sub_mul, Int.one_mul] at hnon hb
  omega

#print axioms stable_greatest
#print axioms greatest_feasible
#print axioms unit_threshold_of_gap

end MathCan.MICAtomicClosure

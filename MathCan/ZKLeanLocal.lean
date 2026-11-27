import MathCan.ZKLeanPoly

/-! ZKL-23: a local implication can justify deletion in an arbitrary context.
All rows and wires are the original global rows and wire IDs. The abstract
context premises must be established by a separately reviewed full-matrix
binding mechanism; a SHA256 receipt is not a Lean proof of these premises.
-/
namespace MathCan.ZKLean.Local
open MathCan.ZKLean
open MathCan.ZKLean.Poly

theorem context_subset (pre post : List Row) (target : Row) :
    RowSubset (pre ++ post) (pre ++ target :: post) := by
  intro r hr
  rcases List.mem_append.mp hr with hp | ht
  · exact List.mem_append.mpr (Or.inl hp)
  · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr ht)))

theorem lift_local_delete (s : Shape) (pre post localRows : List Row) (target : Row)
    (hs : wellFormed (withRows s (pre ++ target :: post)))
    (hsub : RowSubset localRows (pre ++ post))
    (himp : ∀ w : Assignment, w 0 = 1 →
      holds s.modulus w localRows → rowHolds s.modulus w target)
    (x : List Nat) :
    accepts (withRows s (pre ++ target :: post)) x ↔
      accepts (withRows s (pre ++ post)) x := by
  have hsub' := context_subset pre post target
  constructor
  · intro ha
    rcases ha with ⟨_, w, hw, hx, hr⟩
    exact ⟨wellFormed_withRows (withRows s (pre ++ target :: post)) (pre ++ post) hs hsub',
           w, hw, hx, holds_of_rowSubset hsub' hr⟩
  · intro ha
    rcases ha with ⟨_, w, hw, hx, hr⟩
    refine ⟨hs, w, hw, hx, ?_⟩
    have ht := himp w hw.1 (holds_of_rowSubset hsub hr)
    intro r hm
    rcases List.mem_append.mp hm with hp | hright
    · exact hr r (List.mem_append.mpr (Or.inl hp))
    · rcases List.mem_cons.mp hright with he | hm'
      · subst r
        exact ht
      · exact hr r (List.mem_append.mpr (Or.inr hm'))

theorem checked_local_poly_delete
    (s : Shape) (pre post localRows : List Row) (target : Row)
    (ws : List Multiplier) (correction : PPoly)
    (hs : wellFormed (withRows s (pre ++ target :: post)))
    (hsub : RowSubset localRows (pre ++ post))
    (hweights : covers (ws.map Multiplier.row) localRows = true)
    (hc : polyCheck s.modulus target ws correction = true)
    (x : List Nat) :
    accepts (withRows s (pre ++ target :: post)) x ↔
      accepts (withRows s (pre ++ post)) x := by
  apply lift_local_delete s pre post localRows target hs hsub
  intro w hz hr
  apply poly_sound s.modulus w hz target ws correction hc
  intro item hm
  exact hr item.row (covers_sound _ _ hweights item.row
    (List.mem_map.mpr ⟨item, hm, rfl⟩))

#print axioms lift_local_delete
#print axioms checked_local_poly_delete


/-! ZKL-24: interpret the certificate's retained indices in the original
ordered matrix. A row at the deleted position cannot discharge a retained
premise, even if the concrete row value occurs elsewhere. -/
private theorem lookup_mem (rows : List Row) (j : Nat) (r : Row)
    (h : rows[j]? = some r) : r ∈ rows := by
  induction rows generalizing j with
  | nil =>
    change none = some r at h
    cases h
  | cons a tail ih =>
    cases j with
    | zero =>
      change some a = some r at h
      exact List.mem_cons.mpr (Or.inl (Option.some.inj h).symm)
    | succ j =>
      change tail[j]? = some r at h
      exact List.mem_cons.mpr (Or.inr (ih j h))

private theorem lookup_mem_erase (rows : List Row) (i j : Nat) (r : Row)
    (hne : j ≠ i) (h : rows[j]? = some r) : r ∈ rows.eraseIdx i := by
  induction rows generalizing i j with
  | nil =>
    change none = some r at h
    cases h
  | cons a tail ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hne rfl)
      | succ j =>
        change tail[j]? = some r at h
        change r ∈ tail
        exact lookup_mem tail j r h
    | succ i =>
      cases j with
      | zero =>
        change some a = some r at h
        change r ∈ a :: tail.eraseIdx i
        exact List.mem_cons.mpr (Or.inl (Option.some.inj h).symm)
      | succ j =>
        change tail[j]? = some r at h
        change r ∈ a :: tail.eraseIdx i
        exact List.mem_cons.mpr (Or.inr (ih i j
          (fun he => hne (congrArg Nat.succ he)) h))

theorem indexed_subset_erase (rows : List Row) (i : Nat)
    (refs : List (Nat × Row))
    (hpos : ∀ q ∈ refs, q.1 ≠ i ∧ rows[q.1]? = some q.2) :
    RowSubset (refs.map Prod.snd) (rows.eraseIdx i) := by
  intro r hr
  rcases List.mem_map.mp hr with ⟨q, hq, he⟩
  rcases hpos q hq with ⟨hne, hlookup⟩
  rw [← he]
  exact lookup_mem_erase rows i q.1 q.2 hne hlookup

private theorem mem_original_or_erased (rows : List Row) (i : Nat)
    (target : Row) (ht : rows[i]? = some target) :
    ∀ r ∈ rows, r = target ∨ r ∈ rows.eraseIdx i := by
  induction rows generalizing i with
  | nil =>
    change none = some target at ht
    cases ht
  | cons a tail ih =>
    cases i with
    | zero =>
      change some a = some target at ht
      intro r hr
      change r = target ∨ r ∈ tail
      rcases List.mem_cons.mp hr with he | hm
      · exact Or.inl (he.trans (Option.some.inj ht))
      · exact Or.inr hm
    | succ i =>
      change tail[i]? = some target at ht
      intro r hr
      change r = target ∨ r ∈ a :: tail.eraseIdx i
      rcases List.mem_cons.mp hr with he | hm
      · exact Or.inr (List.mem_cons.mpr (Or.inl he))
      · rcases ih i ht r hm with he | hm'
        · exact Or.inl he
        · exact Or.inr (List.mem_cons.mpr (Or.inr hm'))

private theorem erased_subset (rows : List Row) (i : Nat) :
    RowSubset (rows.eraseIdx i) rows := by
  induction rows generalizing i with
  | nil =>
    intro r hr
    change r ∈ ([] : List Row) at hr
    exact False.elim (List.not_mem_nil hr)
  | cons a tail ih =>
    cases i with
    | zero =>
      intro r hr
      change r ∈ tail at hr
      exact List.mem_cons.mpr (Or.inr hr)
    | succ i =>
      intro r hr
      change r ∈ a :: tail.eraseIdx i at hr
      rcases List.mem_cons.mp hr with he | hm
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons.mpr (Or.inr (ih i r hm))

theorem checked_indexed_poly_delete
    (s : Shape) (i : Nat) (target : Row) (refs : List (Nat × Row))
    (ws : List Multiplier) (correction : PPoly)
    (hs : wellFormed s) (_hi : i < s.rows.length)
    (ht : s.rows[i]? = some target)
    (hpos : ∀ q ∈ refs, q.1 ≠ i ∧ s.rows[q.1]? = some q.2)
    (hweights : covers (ws.map Multiplier.row) (refs.map Prod.snd) = true)
    (hc : polyCheck s.modulus target ws correction = true) (x : List Nat) :
    accepts s x ↔ accepts (withRows s (s.rows.eraseIdx i)) x := by
  have hsub := indexed_subset_erase s.rows i refs hpos
  have hret := erased_subset s.rows i
  constructor
  · intro ha
    rcases ha with ⟨_, w, hw, hx, hr⟩
    exact ⟨wellFormed_withRows s (s.rows.eraseIdx i) hs hret,
           w, hw, hx, holds_of_rowSubset hret hr⟩
  · intro ha
    rcases ha with ⟨_, w, hw, hx, hr⟩
    refine ⟨hs, w, hw, hx, ?_⟩
    have hlocal := holds_of_rowSubset hsub hr
    have htarget : rowHolds s.modulus w target := by
      apply poly_sound s.modulus w hw.1 target ws correction hc
      intro item hm
      exact hlocal item.row (covers_sound _ _ hweights item.row
        (List.mem_map.mpr ⟨item, hm, rfl⟩))
    intro r hm
    rcases mem_original_or_erased s.rows i target ht r hm with he | hmem
    · subst r
      exact htarget
    · exact hr r hmem

#print axioms lookup_mem_erase
#print axioms mem_original_or_erased
#print axioms erased_subset
#print axioms indexed_subset_erase
#print axioms checked_indexed_poly_delete

end MathCan.ZKLean.Local

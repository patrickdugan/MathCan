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
theorem indexed_subset_erase (rows : List Row) (i : Nat)
    (refs : List (Nat × Row))
    (hpos : ∀ q ∈ refs, q.1 ≠ i ∧ rows[q.1]? = some q.2) :
    RowSubset (refs.map Prod.snd) (rows.eraseIdx i) := by
  intro r hr
  rcases List.mem_map.mp hr with ⟨q, hq, he⟩
  rcases hpos q hq with ⟨hne, hlookup⟩
  have hmem : q.2 ∈ rows.eraseIdx i := by
    by_cases hlt : q.1 < i
    · apply List.mem_of_getElem? (i := q.1)
      rw [List.getElem?_eraseIdx, if_pos hlt]
      exact hlookup
    · have hlt' : ¬ q.1 - 1 < i := by omega
      have hplus : q.1 - 1 + 1 = q.1 := by omega
      apply List.mem_of_getElem? (i := q.1 - 1)
      rw [List.getElem?_eraseIdx, if_neg hlt', hplus]
      exact hlookup
  rw [← he]
  exact hmem

theorem checked_indexed_poly_delete
    (s : Shape) (i : Nat) (target : Row) (refs : List (Nat × Row))
    (ws : List Multiplier) (correction : PPoly)
    (hs : wellFormed s) (hi : i < s.rows.length) (ht : s.rows[i] = target)
    (hpos : ∀ q ∈ refs, q.1 ≠ i ∧ s.rows[q.1]? = some q.2)
    (hweights : covers (ws.map Multiplier.row) (refs.map Prod.snd) = true)
    (hc : polyCheck s.modulus target ws correction = true) (x : List Nat) :
    accepts s x ↔ accepts (withRows s (s.rows.eraseIdx i)) x := by
  have hsplit : s.rows.take i ++ target :: s.rows.drop (i + 1) = s.rows := by
    rw [← ht, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hdel := List.eraseIdx_eq_take_drop_succ s.rows i
  have hs' : wellFormed (withRows s (s.rows.take i ++ target :: s.rows.drop (i + 1))) := by
    rw [hsplit]
    cases s
    exact hs
  have hsub := indexed_subset_erase s.rows i refs hpos
  rw [hdel] at hsub
  have h := checked_local_poly_delete s (s.rows.take i) (s.rows.drop (i + 1))
    (refs.map Prod.snd) target ws correction hs' hsub hweights hc x
  rw [hsplit, ← hdel] at h
  cases s
  exact h

#print axioms indexed_subset_erase
#print axioms checked_indexed_poly_delete

end MathCan.ZKLean.Local

import MathCan.ZKLeanLocal

/-! ZKL-28: compositional certificates.
Sequential and simultaneous (dependency-aware) deletion, public-interface
invariance, global wire substitution, contextual polynomial implication,
chunked verification, index transport, and an adversarial cyclic example.
Core Lean only; no axioms beyond propext/Quot.sound. -/
namespace MathCan.ZKLean.Compose
open MathCan.ZKLean
open MathCan.ZKLean.Poly
open MathCan.ZKLean.Local
open MathCan.ZKLean.Algebra (residual row_residual_dvd evalQ)

/-! Helper lemmas about indexed lists. -/

theorem erase_subset (rows : List Row) (i : Nat) :
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

theorem mem_index : ∀ (rows : List Row) (r : Row), r ∈ rows → ∃ j : Nat, rows[j]? = some r := by
  intro rows
  induction rows with
  | nil =>
    intro r hr
    exact False.elim (List.not_mem_nil hr)
  | cons a tl ih =>
    intro r hr
    rcases List.mem_cons.mp hr with he | hm
    · exact ⟨0, by rw [he]; rfl⟩
    · rcases ih r hm with ⟨j, hj⟩
      exact ⟨j + 1, hj⟩

theorem mem_original_or_erased' (rows : List Row) (i : Nat)
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

/-! 1. Sequential deletion. The second certificate's indices address the
already-deleted matrix. -/

theorem seq_delete (s : Shape) (i j : Nat) (t1 t2 : Row)
    (refs1 refs2 : List (Nat × Row)) (ws1 ws2 : List Multiplier)
    (c1 c2 : PPoly) (hs : wellFormed s)
    (hi : i < s.rows.length) (ht1 : s.rows[i]? = some t1)
    (hpos1 : ∀ q ∈ refs1, q.1 ≠ i ∧ s.rows[q.1]? = some q.2)
    (hw1 : covers (ws1.map Multiplier.row) (refs1.map Prod.snd) = true)
    (hc1 : polyCheck s.modulus t1 ws1 c1 = true)
    (hj : j < (s.rows.eraseIdx i).length)
    (ht2 : (s.rows.eraseIdx i)[j]? = some t2)
    (hpos2 : ∀ q ∈ refs2, q.1 ≠ j ∧ (s.rows.eraseIdx i)[q.1]? = some q.2)
    (hw2 : covers (ws2.map Multiplier.row) (refs2.map Prod.snd) = true)
    (hc2 : polyCheck s.modulus t2 ws2 c2 = true) (x : List Nat) :
    accepts s x ↔ accepts (withRows s ((s.rows.eraseIdx i).eraseIdx j)) x := by
  have h1 := checked_indexed_poly_delete s i t1 refs1 ws1 c1 hs hi ht1 hpos1 hw1 hc1 x
  have hs' : wellFormed (withRows s (s.rows.eraseIdx i)) :=
    wellFormed_withRows s _ hs (erase_subset _ _)
  have h2 := checked_indexed_poly_delete (withRows s (s.rows.eraseIdx i)) j t2
    refs2 ws2 c2 hs' hj ht2 hpos2 hw2 hc2 x
  exact h1.trans h2

#print axioms seq_delete

/-! 2. Simultaneous dependency-aware deletion. -/

def keepFrom (D : List Nat) : Nat → List Row → List Row
  | _, [] => []
  | k, r :: rs => if k ∈ D then keepFrom D (k + 1) rs else r :: keepFrom D (k + 1) rs

/-- Delete every row whose index lies in `D`. -/
def eraseAll (rows : List Row) (D : List Nat) : List Row := keepFrom D 0 rows

theorem keepFrom_subset (D : List Nat) :
    ∀ (rows : List Row) (k : Nat), RowSubset (keepFrom D k rows) rows := by
  intro rows
  induction rows with
  | nil =>
    intro k r hr
    exact False.elim (List.not_mem_nil hr)
  | cons a tl ih =>
    intro k r hr
    simp only [keepFrom] at hr
    split at hr
    · exact List.mem_cons.mpr (Or.inr (ih _ r hr))
    · rcases List.mem_cons.mp hr with he | hm
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons.mpr (Or.inr (ih _ r hm))

theorem keepFrom_mem (D : List Nat) :
    ∀ (rows : List Row) (k j : Nat) (r : Row),
      rows[j]? = some r → k + j ∉ D → r ∈ keepFrom D k rows := by
  intro rows
  induction rows with
  | nil =>
    intro k j r h _
    change none = some r at h
    cases h
  | cons a tl ih =>
    intro k j r h hk
    cases j with
    | zero =>
      change some a = some r at h
      have hk' : k ∉ D := hk
      have e : r = a := (Option.some.inj h).symm
      subst e
      simp [keepFrom, hk']
    | succ j =>
      change tl[j]? = some r at h
      have hk2 : k + 1 + j ∉ D := by
        rw [show k + 1 + j = k + (j + 1) by omega]; exact hk
      have hm := ih (k + 1) j r h hk2
      simp only [keepFrom]
      split
      · exact hm
      · exact List.mem_cons.mpr (Or.inr hm)

theorem eraseAll_subset (rows : List Row) (D : List Nat) :
    RowSubset (eraseAll rows D) rows := keepFrom_subset D rows 0

theorem eraseAll_mem (rows : List Row) (D : List Nat) (j : Nat) (r : Row)
    (h : rows[j]? = some r) (hj : j ∉ D) : r ∈ eraseAll rows D :=
  keepFrom_mem D rows 0 j r h (by simpa using hj)

/-- Every reference of a deleted target is outside `D` or has strictly smaller rank. -/
def RankOK (D : List Nat) (refs : Nat → List (Nat × Row)) (rank : Nat → Nat) : Prop :=
  ∀ t ∈ D, ∀ q ∈ refs t, q.1 ∉ D ∨ (q.1 ∈ D ∧ rank q.1 < rank t)

theorem simultaneous_delete (s : Shape) (D : List Nat) (_hD : D.Nodup)
    (refs : Nat → List (Nat × Row)) (ws : Nat → List Multiplier)
    (corr : Nat → PPoly) (rank : Nat → Nat)
    (hs : wellFormed s)
    (hcert : ∀ t ∈ D, ∃ target, s.rows[t]? = some target ∧
      (∀ q ∈ refs t, q.1 ≠ t ∧ s.rows[q.1]? = some q.2) ∧
      covers ((ws t).map Multiplier.row) ((refs t).map Prod.snd) = true ∧
      polyCheck s.modulus target (ws t) (corr t) = true)
    (hrank : RankOK D refs rank) (x : List Nat) :
    accepts s x ↔ accepts (withRows s (eraseAll s.rows D)) x := by
  have hsub := eraseAll_subset s.rows D
  constructor
  · intro ha
    rcases ha with ⟨_, w, hw, hx, hr⟩
    exact ⟨wellFormed_withRows s _ hs hsub, w, hw, hx, holds_of_rowSubset hsub hr⟩
  · intro ha
    rcases ha with ⟨_, w, hw, hx, hr⟩
    have hr' : holds s.modulus w (eraseAll s.rows D) := hr
    refine ⟨hs, w, hw, hx, ?_⟩
    have key : ∀ n, ∀ t, t ∈ D → rank t = n → ∀ target, s.rows[t]? = some target →
        rowHolds s.modulus w target := by
      intro n
      induction n using Nat.strongRecOn with
      | _ n ih =>
        intro t htD hrt target htg
        obtain ⟨tg, htg', hpos, hcov, hchk⟩ := hcert t htD
        have e : tg = target := by
          rw [htg] at htg'
          exact (Option.some.inj htg').symm
        subst e
        apply poly_sound s.modulus w hw.1 tg (ws t) (corr t) hchk
        intro item hm
        have hmem : item.row ∈ (refs t).map Prod.snd :=
          covers_sound _ _ hcov item.row (List.mem_map.mpr ⟨item, hm, rfl⟩)
        obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
        rw [← hqe]
        rcases hrank t htD q hq with hout | ⟨hin, hlt⟩
        · exact hr' q.2 (eraseAll_mem s.rows D q.1 q.2 (hpos q hq).2 hout)
        · exact ih (rank q.1) (hrt ▸ hlt) q.1 hin rfl q.2 (hpos q hq).2
    intro r hm
    obtain ⟨j, hj⟩ := mem_index s.rows r hm
    by_cases hjD : j ∈ D
    · exact key (rank j) j hjD rfl r hj
    · exact hr' r (eraseAll_mem s.rows D j r hj hjD)

#print axioms simultaneous_delete

theorem simultaneous_delete_outside (s : Shape) (D : List Nat) (hD : D.Nodup)
    (refs : Nat → List (Nat × Row)) (ws : Nat → List Multiplier)
    (corr : Nat → PPoly) (hs : wellFormed s)
    (hcert : ∀ t ∈ D, ∃ target, s.rows[t]? = some target ∧
      (∀ q ∈ refs t, q.1 ≠ t ∧ s.rows[q.1]? = some q.2) ∧
      covers ((ws t).map Multiplier.row) ((refs t).map Prod.snd) = true ∧
      polyCheck s.modulus target (ws t) (corr t) = true)
    (hout : ∀ t ∈ D, ∀ q ∈ refs t, q.1 ∉ D) (x : List Nat) :
    accepts s x ↔ accepts (withRows s (eraseAll s.rows D)) x :=
  simultaneous_delete s D hD refs ws corr (fun _ => 0) hs hcert
    (fun t ht q hq => Or.inl (hout t ht q hq)) x

#print axioms simultaneous_delete_outside

/-! 3. Public wire ordering. -/

theorem withRows_interface (s : Shape) (rs : List Row) :
    (withRows s rs).publicWires = s.publicWires ∧
    (withRows s rs).modulus = s.modulus ∧ (withRows s rs).wires = s.wires :=
  ⟨rfl, rfl, rfl⟩

theorem eraseIdx_interface (s : Shape) (i : Nat) :
    (withRows s (s.rows.eraseIdx i)).publicWires = s.publicWires ∧
    (withRows s (s.rows.eraseIdx i)).modulus = s.modulus ∧
    (withRows s (s.rows.eraseIdx i)).wires = s.wires :=
  ⟨rfl, rfl, rfl⟩

theorem seq_eraseIdx_interface (s : Shape) (i j : Nat) :
    (withRows s ((s.rows.eraseIdx i).eraseIdx j)).publicWires = s.publicWires ∧
    (withRows s ((s.rows.eraseIdx i).eraseIdx j)).modulus = s.modulus ∧
    (withRows s ((s.rows.eraseIdx i).eraseIdx j)).wires = s.wires :=
  ⟨rfl, rfl, rfl⟩

theorem eraseAll_interface (s : Shape) (D : List Nat) :
    (withRows s (eraseAll s.rows D)).publicWires = s.publicWires ∧
    (withRows s (eraseAll s.rows D)).modulus = s.modulus ∧
    (withRows s (eraseAll s.rows D)).wires = s.wires :=
  ⟨rfl, rfl, rfl⟩

def zeroRow1 : Row := ⟨[⟨1, 1⟩], [⟨0, 1⟩], []⟩
def ordA : Shape := ⟨7, 3, [1, 2], [zeroRow1]⟩
def ordB : Shape := ⟨7, 3, [2, 1], [zeroRow1]⟩
def wOrd : Assignment := fun i => [1, 0, 1].getD i 0

theorem public_order_matters : accepts ordA [0, 1] ∧ ¬ accepts ordB [0, 1] := by
  constructor
  · refine ⟨by unfold wellFormed; decide, wOrd, ⟨by decide, by decide⟩, by decide, ?_⟩
    intro r hr
    have e : r = zeroRow1 := List.mem_singleton.mp hr
    subst e
    unfold rowHolds
    decide
  · rintro ⟨_, w, hw, hx, hr⟩
    have hx' : [w 2, w 1] = [0, 1] := hx
    have h2 : w 1 = 1 := (List.cons.inj (List.cons.inj hx').2).1
    have hrow := hr zeroRow1 (List.mem_singleton.mpr rfl)
    unfold rowHolds at hrow
    simp [zeroRow1, ordB, evalLC, hw.1, h2] at hrow

#print axioms public_order_matters

/-! 6. Chunked verification. -/

theorem holds_flatten (p : Nat) (w : Assignment) (chunks : List (List Row)) :
    holds p w chunks.flatten ↔ ∀ c ∈ chunks, holds p w c := by
  induction chunks with
  | nil =>
    constructor
    · intro _ c hc
      exact False.elim (List.not_mem_nil hc)
    · intro _ r hr
      exact False.elim (List.not_mem_nil hr)
  | cons c cs ih =>
    have e : (c :: cs).flatten = c ++ cs.flatten := rfl
    rw [e, holds_append, ih]
    constructor
    · rintro ⟨h1, h2⟩ d hd
      rcases List.mem_cons.mp hd with he | hm
      · rw [he]; exact h1
      · exact h2 d hm
    · intro h
      exact ⟨h c (List.mem_cons.mpr (Or.inl rfl)),
             fun d hd => h d (List.mem_cons.mpr (Or.inr hd))⟩

theorem covers_of_subset (need haveRows : List Row) (h : RowSubset need haveRows) :
    covers need haveRows = true :=
  List.all_eq_true.mpr fun r hr => decide_eq_true (h r hr)

theorem covers_flatten (needs : List (List Row)) (haveRows : List Row) :
    covers needs.flatten haveRows = true ↔ ∀ c ∈ needs, covers c haveRows = true := by
  constructor
  · intro h c hc
    apply covers_of_subset
    intro r hr
    exact covers_sound _ _ h r (List.mem_flatten.mpr ⟨c, hc, hr⟩)
  · intro h
    apply covers_of_subset
    intro r hr
    obtain ⟨c, hc, hrc⟩ := List.mem_flatten.mp hr
    exact covers_sound _ _ (h c hc) r hrc

theorem getElem?_append_offset {α : Type} (pre c : List α) (k : Nat) :
    (pre ++ c)[pre.length + k]? = c[k]? := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    have e : (a :: pre).length + k = (pre.length + k) + 1 := by
      simp only [List.length_cons]; omega
    rw [e]
    simpa using ih

#print axioms holds_flatten
#print axioms covers_flatten
#print axioms getElem?_append_offset

/-! 7. Index transport after multiple deletions. -/

def cntFrom (D : List Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, j + 1 => (if k ∈ D then 1 else 0) + cntFrom D (k + 1) j

/-- New index of original row `j`, or `none` when `j` is deleted. -/
def transport (D : List Nat) (j : Nat) : Option Nat :=
  if j ∈ D then none else some (j - cntFrom D 0 j)

theorem cntFrom_le (D : List Nat) : ∀ (j k : Nat), cntFrom D k j ≤ j := by
  intro j
  induction j with
  | zero => intro k; simp [cntFrom]
  | succ j ih =>
    intro k
    have := ih (k + 1)
    simp only [cntFrom]
    split <;> omega

theorem keepFrom_index (D : List Nat) :
    ∀ (rows : List Row) (k j : Nat), k + j ∉ D →
      (keepFrom D k rows)[j - cntFrom D k j]? = rows[j]? := by
  intro rows
  induction rows with
  | nil => intro k j _; simp [keepFrom]
  | cons a tl ih =>
    intro k j hk
    cases j with
    | zero =>
      have hk' : k ∉ D := hk
      have e : cntFrom D k 0 = 0 := rfl
      rw [e, Nat.sub_zero]
      simp [keepFrom, hk']
    | succ j =>
      have hk2 : k + 1 + j ∉ D := by
        rw [show k + 1 + j = k + (j + 1) by omega]; exact hk
      have ih' := ih (k + 1) j hk2
      have hle := cntFrom_le D j (k + 1)
      by_cases hkD : k ∈ D
      · have e : cntFrom D k (j + 1) = 1 + cntFrom D (k + 1) j := by
          simp [cntFrom, hkD]
        have e2 : j + 1 - (1 + cntFrom D (k + 1) j) = j - cntFrom D (k + 1) j := by omega
        rw [e, e2]
        simpa [keepFrom, hkD] using ih'
      · have e : cntFrom D k (j + 1) = cntFrom D (k + 1) j := by
          simp [cntFrom, hkD]
        have e2 : j + 1 - cntFrom D (k + 1) j = (j - cntFrom D (k + 1) j) + 1 := by omega
        rw [e, e2]
        simp [keepFrom, hkD, ih']

theorem transport_none_iff (D : List Nat) (j : Nat) :
    transport D j = none ↔ j ∈ D := by
  unfold transport
  split
  · rename_i h; exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h; exact ⟨fun e => (nomatch e), fun h' => absurd h' h⟩

theorem transport_correct (rows : List Row) (D : List Nat) (j : Nat) (hj : j ∉ D) :
    ∃ j', transport D j = some j' ∧ (eraseAll rows D)[j']? = rows[j]? :=
  ⟨j - cntFrom D 0 j, by simp [transport, hj],
   keepFrom_index D rows 0 j (by simpa using hj)⟩

#print axioms keepFrom_index
#print axioms transport_none_iff
#print axioms transport_correct

/-! 8. Adversarial cyclic example: each row is implied by the other. -/

def cycR1 : Row := ⟨[⟨1, 1⟩], [⟨0, 1⟩], [⟨2, 1⟩]⟩
def cycR2 : Row := ⟨[⟨2, 1⟩], [⟨0, 1⟩], [⟨1, 1⟩]⟩
def cycShape : Shape := ⟨7, 3, [1, 2], [cycR1, cycR2]⟩

theorem cyc_delete_0 (x : List Nat) :
    accepts cycShape x ↔ accepts (withRows cycShape (cycShape.rows.eraseIdx 0)) x :=
  checked_indexed_poly_delete cycShape 0 cycR1 [(1, cycR2)] [⟨-1, [], cycR2⟩] []
    (by unfold wellFormed; decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) x

theorem cyc_delete_1 (x : List Nat) :
    accepts cycShape x ↔ accepts (withRows cycShape (cycShape.rows.eraseIdx 1)) x :=
  checked_indexed_poly_delete cycShape 1 cycR2 [(0, cycR1)] [⟨-1, [], cycR1⟩] []
    (by unfold wellFormed; decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) x

def cycRefs : Nat → List (Nat × Row)
  | 0 => [(1, cycR2)]
  | _ => [(0, cycR1)]

theorem cyc_no_rank_pair : ∀ rank : Nat → Nat, ¬ (rank 0 < rank 1 ∧ rank 1 < rank 0) := by
  intro rank h
  omega

theorem cyc_no_rank : ∀ rank : Nat → Nat, ¬ RankOK [0, 1] cycRefs rank := by
  intro rank h
  have h0 := h 0 (by simp) (1, cycR2) (by simp [cycRefs])
  have h1 := h 1 (by simp) (0, cycR1) (by simp [cycRefs])
  simp at h0 h1
  omega

def wCyc : Assignment := fun i => [1, 1, 2].getD i 0

theorem cyc_eraseAll : eraseAll cycShape.rows [0, 1] = [] := by decide

theorem cyc_joint_unsound :
    accepts (withRows cycShape []) [1, 2] ∧ ¬ accepts cycShape [1, 2] := by
  constructor
  · refine ⟨by unfold wellFormed; decide, wCyc, ⟨by decide, by decide⟩, by decide, ?_⟩
    intro r hr
    exact False.elim (List.not_mem_nil hr)
  · rintro ⟨_, w, hw, hx, hr⟩
    have hx' : [w 1, w 2] = [1, 2] := hx
    have h1 : w 1 = 1 := (List.cons.inj hx').1
    have h2 : w 2 = 2 := (List.cons.inj (List.cons.inj hx').2).1
    have hrow := hr cycR1 (by simp [cycShape])
    unfold rowHolds at hrow
    simp [cycR1, cycShape, evalLC, hw.1, h1, h2] at hrow

theorem cyc_joint_not_equiv :
    ¬ (accepts cycShape [1, 2] ↔
        accepts (withRows cycShape (eraseAll cycShape.rows [0, 1])) [1, 2]) := by
  rw [cyc_eraseAll]
  intro h
  exact cyc_joint_unsound.2 (h.mpr cyc_joint_unsound.1)

#print axioms cyc_delete_0
#print axioms cyc_delete_1
#print axioms cyc_no_rank_pair
#print axioms cyc_no_rank
#print axioms cyc_eraseAll
#print axioms cyc_joint_unsound
#print axioms cyc_joint_not_equiv

/-! 5. Polynomial implication under contextual assumptions. -/

structure AMult where
  coeff : Int
  mon : Mon
  poly : PPoly

def combinationA : List AMult → PPoly
  | [] => []
  | t :: ts => timesMon t.coeff t.mon t.poly ++ combinationA ts

theorem combinationA_dvd (p : Nat) (w : Assignment) (as : List AMult)
    (h : ∀ t ∈ as, (p : Int) ∣ evalP w t.poly) :
    (p : Int) ∣ evalP w (combinationA as) := by
  induction as with
  | nil => simp [combinationA, evalP]
  | cons t ts ih =>
    have ht := h t (List.mem_cons.mpr (Or.inl rfl))
    have hts : (p : Int) ∣ evalP w (combinationA ts) :=
      ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))
    rw [combinationA, eval_appendP, eval_timesMon]
    exact Int.dvd_add (Int.dvd_mul_of_dvd_right ht) hts

def rhsA (p : Nat) (ws : List Multiplier) (as : List AMult) (correction : PPoly) : PPoly :=
  combinationP ws ++ combinationA as ++ timesMon (p : Int) [] correction

def polyCheckA (p : Nat) (target : Row) (ws : List Multiplier) (as : List AMult)
    (correction : PPoly) : Bool :=
  decide (normalizeP (liftQ (residual target) ++ timesMon (-1) [] (rhsA p ws as correction)) = [])

theorem poly_sound_ctx (p : Nat) (w : Assignment) (hz : w 0 = 1)
    (target : Row) (ws : List Multiplier) (as : List AMult) (correction : PPoly)
    (hc : polyCheckA p target ws as correction = true)
    (h : ∀ t ∈ ws, rowHolds p w t.row)
    (hA : ∀ t ∈ as, (p : Int) ∣ evalP w t.poly) :
    rowHolds p w target := by
  have he : normalizeP (liftQ (residual target) ++ timesMon (-1) [] (rhsA p ws as correction)) = [] :=
    of_decide_eq_true hc
  have hv := congrArg (evalP w) he
  simp only [eval_normalizeP, eval_appendP, eval_timesMon, evalMon, Int.mul_one,
    eval_liftQ w hz, evalP] at hv
  have eqv : evalQ w (residual target) = evalP w (rhsA p ws as correction) := by omega
  apply (row_residual_dvd p w hz target).mpr
  rw [eqv, rhsA, eval_appendP, eval_appendP, eval_timesMon]
  simp only [evalMon, Int.mul_one]
  exact Int.dvd_add (Int.dvd_add (combinationP_dvd p w hz ws h) (combinationA_dvd p w as hA))
    ⟨evalP w correction, rfl⟩

theorem polyCheckA_nil (p : Nat) (target : Row) (ws : List Multiplier) (c : PPoly) :
    polyCheckA p target ws [] c = polyCheck p target ws c := by
  have e : rhsA p ws [] c = rhs p ws c := by simp [rhsA, combinationA, rhs]
  unfold polyCheckA polyCheck
  rw [e]

theorem assump_of_row (p : Nat) (w : Assignment) (hz : w 0 = 1) (r : Row)
    (h : rowHolds p w r) : (p : Int) ∣ evalP w (liftQ (residual r)) := by
  rw [eval_liftQ w hz]
  exact (row_residual_dvd p w hz r).mp h

theorem discharge_assumptions (p : Nat) (w : Assignment) (hz : w 0 = 1)
    (as : List AMult)
    (h : ∀ t ∈ as, ∃ r, t.poly = liftQ (residual r) ∧ rowHolds p w r) :
    ∀ t ∈ as, (p : Int) ∣ evalP w t.poly := by
  intro t ht
  obtain ⟨r, he, hr⟩ := h t ht
  rw [he]
  exact assump_of_row p w hz r hr

theorem poly_sound_ctx_rows (p : Nat) (w : Assignment) (hz : w 0 = 1)
    (target : Row) (ws : List Multiplier) (as : List AMult) (correction : PPoly)
    (hc : polyCheckA p target ws as correction = true)
    (h : ∀ t ∈ ws, rowHolds p w t.row)
    (hA : ∀ t ∈ as, ∃ r, t.poly = liftQ (residual r) ∧ rowHolds p w r) :
    rowHolds p w target :=
  poly_sound_ctx p w hz target ws as correction hc h (discharge_assumptions p w hz as hA)

#print axioms combinationA_dvd
#print axioms poly_sound_ctx
#print axioms polyCheckA_nil
#print axioms assump_of_row
#print axioms discharge_assumptions
#print axioms poly_sound_ctx_rows

/-! 4a. Global witness-wire renaming. -/

def renameLC (σ : Nat → Nat) (l : LC) : LC := l.map fun t => ⟨σ t.wire, t.coeff⟩
def renameRow (σ : Nat → Nat) (r : Row) : Row :=
  ⟨renameLC σ r.a, renameLC σ r.b, renameLC σ r.c⟩
def renameShape (σ : Nat → Nat) (s : Shape) : Shape :=
  withRows s (s.rows.map (renameRow σ))

def lcSum (w : Assignment) (l : LC) : Nat := (l.map fun t => t.coeff * w t.wire).sum

theorem foldl_lcSum (w : Assignment) :
    ∀ (l : LC) (acc : Nat),
      l.foldl (fun acc t => acc + t.coeff * w t.wire) acc = acc + lcSum w l := by
  intro l
  induction l with
  | nil => intro acc; simp [lcSum]
  | cons t ts ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih]
    simp only [lcSum, List.map_cons, List.sum_cons]
    omega

theorem evalLC_eq (p : Nat) (w : Assignment) (l : LC) :
    evalLC p w l = lcSum w l % p := by
  unfold evalLC
  rw [foldl_lcSum]
  simp

theorem lcSum_rename (σ : Nat → Nat) (w : Assignment) (l : LC) :
    lcSum w (renameLC σ l) = lcSum (fun i => w (σ i)) l := by
  simp [lcSum, renameLC, List.map_map, Function.comp_def]

theorem evalLC_rename (p : Nat) (σ : Nat → Nat) (w : Assignment) (l : LC) :
    evalLC p w (renameLC σ l) = evalLC p (fun i => w (σ i)) l := by
  rw [evalLC_eq, evalLC_eq, lcSum_rename]

theorem rowHolds_rename (p : Nat) (σ : Nat → Nat) (w : Assignment) (r : Row) :
    rowHolds p w (renameRow σ r) ↔ rowHolds p (fun i => w (σ i)) r := by
  simp only [rowHolds, renameRow, evalLC_rename]

theorem holds_rename (p : Nat) (σ : Nat → Nat) (w : Assignment) (rows : List Row) :
    holds p w (rows.map (renameRow σ)) ↔ holds p (fun i => w (σ i)) rows := by
  constructor
  · intro h r hr
    exact (rowHolds_rename p σ w r).mp (h _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
  · intro h r' hr'
    obtain ⟨r, hr, e⟩ := List.mem_map.mp hr'
    rw [← e]
    exact (rowHolds_rename p σ w r).mpr (h r hr)

theorem rowTerms_rename (σ : Nat → Nat) (r : Row) :
    (renameRow σ r).a ++ (renameRow σ r).b ++ (renameRow σ r).c =
      (r.a ++ r.b ++ r.c).map fun t => (⟨σ t.wire, t.coeff⟩ : Term) := by
  simp [renameRow, renameLC, List.map_append]

theorem rename_accepts (s : Shape) (σ τ : Nat → Nat)
    (hτσ : ∀ n, τ (σ n) = n) (_hστ : ∀ n, σ (τ n) = n) (h0 : σ 0 = 0)
    (hpub : ∀ i ∈ s.publicWires, σ i = i)
    (hσb : ∀ n, n < s.wires → σ n < s.wires)
    (hτb : ∀ n, n < s.wires → τ n < s.wires) (x : List Nat) :
    accepts s x ↔ accepts (renameShape σ s) x := by
  have hτ0 : τ 0 = 0 := by
    have := hτσ 0
    rw [h0] at this
    exact this
  constructor
  · rintro ⟨hwf, w, hw, hx, hr⟩
    obtain ⟨hp, hwi, hpb, hn, hrows⟩ := hwf
    refine ⟨⟨hp, hwi, hpb, hn, ?_⟩, fun i => w (τ i), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro r' hr' t' ht'
      obtain ⟨r, hrm, e⟩ := List.mem_map.mp hr'
      rw [← e, rowTerms_rename] at ht'
      obtain ⟨t, ht, e2⟩ := List.mem_map.mp ht'
      rw [← e2]
      have := hrows r hrm t ht
      exact ⟨hσb _ this.1, this.2⟩
    · show w (τ 0) = 1
      rw [hτ0]; exact hw.1
    · intro i hi
      exact hw.2 (τ i) (hτb i hi)
    · have e : (renameShape σ s).publicWires = s.publicWires := rfl
      rw [e]
      rw [← hx]
      apply List.map_congr_left
      intro a ha
      show w (τ a) = w a
      have := hτσ a
      rw [hpub a ha] at this
      rw [this]
    · apply (holds_rename _ σ _ _).mpr
      have e : (fun i => w (τ (σ i))) = w := funext fun i => by rw [hτσ]
      show holds s.modulus (fun i => w (τ (σ i))) s.rows
      rw [e]; exact hr
  · rintro ⟨hwf, w, hw, hx, hr⟩
    obtain ⟨hp, hwi, hpb, hn, hrows⟩ := hwf
    refine ⟨⟨hp, hwi, hpb, hn, ?_⟩, fun i => w (σ i), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro r hrm t ht
      have hmem : (⟨σ t.wire, t.coeff⟩ : Term) ∈
          (renameRow σ r).a ++ (renameRow σ r).b ++ (renameRow σ r).c := by
        rw [rowTerms_rename]
        exact List.mem_map.mpr ⟨t, ht, rfl⟩
      have := hrows (renameRow σ r) (List.mem_map.mpr ⟨r, hrm, rfl⟩) _ hmem
      have hb := hτb _ this.1
      rw [hτσ] at hb
      exact ⟨hb, this.2⟩
    · show w (σ 0) = 1
      rw [h0]; exact hw.1
    · intro i hi
      exact hw.2 (σ i) (hσb i hi)
    · rw [← hx]
      apply List.map_congr_left
      intro a ha
      show w (σ a) = w a
      rw [hpub a ha]
    · exact (holds_rename _ σ _ _).mp hr

#print axioms evalLC_eq
#print axioms holds_rename
#print axioms rename_accepts

/-! 4b. Dead-output elimination. -/

def upd (w : Assignment) (v val : Nat) : Assignment := fun i => if i = v then val else w i

theorem lcSum_upd_avoid (w : Assignment) (v val : Nat) (l : LC)
    (h : ∀ t ∈ l, t.wire ≠ v) : lcSum (upd w v val) l = lcSum w l := by
  unfold lcSum
  congr 1
  apply List.map_congr_left
  intro t ht
  simp [upd, h t ht]

theorem filter_nil_avoid (v : Nat) :
    ∀ (l : LC), l.filter (fun t => decide (t.wire = v)) = [] → ∀ t ∈ l, t.wire ≠ v := by
  intro l
  induction l with
  | nil => intro _ t ht; exact False.elim (List.not_mem_nil ht)
  | cons a tl ih =>
    intro h t ht
    by_cases hv : a.wire = v
    · simp [List.filter_cons, hv] at h
    · simp only [List.filter_cons] at h
      have h' : decide (a.wire = v) = false := by simp [hv]
      rw [h'] at h
      simp only [Bool.false_eq_true, if_false] at h
      rcases List.mem_cons.mp ht with he | hm
      · rw [he]; exact hv
      · exact ih h t hm

theorem lcSum_upd_single (w : Assignment) (v cv val : Nat) :
    ∀ (l : LC), l.filter (fun t => decide (t.wire = v)) = [⟨v, cv⟩] →
      lcSum (upd w v val) l = lcSum (upd w v 0) l + cv * val := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons t ts ih =>
    intro h
    by_cases hv : t.wire = v
    · simp only [List.filter_cons, hv, decide_true, if_true] at h
      have h1 : t = ⟨v, cv⟩ := (List.cons.inj h).1
      have h2 : ts.filter (fun t => decide (t.wire = v)) = [] := (List.cons.inj h).2
      have hav := filter_nil_avoid v ts h2
      have e1 := lcSum_upd_avoid w v val ts hav
      have e2 := lcSum_upd_avoid w v 0 ts hav
      subst h1
      simp only [lcSum, List.map_cons, List.sum_cons, upd, if_true] at e1 e2 ⊢
      omega
    · have h' : decide (t.wire = v) = false := by simp [hv]
      simp only [List.filter_cons, h', Bool.false_eq_true, if_false] at h
      have ih' := ih h
      simp only [lcSum, List.map_cons, List.sum_cons] at ih' ⊢
      have e1 : upd w v val t.wire = w t.wire := by simp [upd, hv]
      have e2 : upd w v 0 t.wire = w t.wire := by simp [upd, hv]
      rw [e1, e2]
      omega

theorem solve_mod (m S cv cinv r : Nat) (hm : 1 < m) (hi : cv * cinv % m = 1)
    (hr : r < m) : ∃ val, val < m ∧ (S + cv * val) % m = r := by
  refine ⟨cinv * (r + (m - S % m)) % m, Nat.mod_lt _ (by omega), ?_⟩
  have h1 : cv * (cinv * (r + (m - S % m)) % m) % m = (r + (m - S % m)) % m := by
    calc cv * (cinv * (r + (m - S % m)) % m) % m
        = cv * (cinv * (r + (m - S % m))) % m := Nat.mul_mod_mod _ _ _
      _ = (cv * cinv) * (r + (m - S % m)) % m := by rw [Nat.mul_assoc]
      _ = ((cv * cinv) % m * ((r + (m - S % m)) % m)) % m := Nat.mul_mod _ _ _
      _ = (1 * ((r + (m - S % m)) % m)) % m := by rw [hi]
      _ = (r + (m - S % m)) % m := by rw [Nat.one_mul, Nat.mod_mod]
  have hS : S % m < m := Nat.mod_lt _ (by omega)
  rw [Nat.add_mod, h1, Nat.add_mod_mod]
  have e : S % m + (r + (m - S % m)) = r + m := by omega
  rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

def DeadSpec (s : Shape) (i v : Nat) (target : Row) (cv cinv : Nat) : Prop :=
  v ≠ 0 ∧ v ∉ s.publicWires ∧ v < s.wires ∧ s.rows[i]? = some target ∧
  (∀ t ∈ target.a, t.wire ≠ v) ∧ (∀ t ∈ target.b, t.wire ≠ v) ∧
  target.c.filter (fun t => decide (t.wire = v)) = [⟨v, cv⟩] ∧
  (cv * cinv) % s.modulus = 1 ∧
  (∀ r ∈ s.rows.eraseIdx i, ∀ t ∈ r.a ++ r.b ++ r.c, t.wire ≠ v)

instance (s : Shape) (i v : Nat) (target : Row) (cv cinv : Nat) :
    Decidable (DeadSpec s i v target cv cinv) := by
  unfold DeadSpec
  infer_instance

def deadOutputCheck (s : Shape) (i v : Nat) (target : Row) (cv cinv : Nat) : Bool :=
  decide (DeadSpec s i v target cv cinv)

theorem evalLC_upd_avoid (p : Nat) (w : Assignment) (v val : Nat) (l : LC)
    (h : ∀ t ∈ l, t.wire ≠ v) : evalLC p (upd w v val) l = evalLC p w l := by
  rw [evalLC_eq, evalLC_eq, lcSum_upd_avoid w v val l h]

theorem dead_output_delete (s : Shape) (i v cv cinv : Nat) (target : Row)
    (hs : wellFormed s)
    (hck : deadOutputCheck s i v target cv cinv = true) (x : List Nat) :
    accepts s x ↔ accepts (withRows s (s.rows.eraseIdx i)) x := by
  have hspec : DeadSpec s i v target cv cinv := of_decide_eq_true hck
  obtain ⟨hv0, hvpub, _hvw, hti, hav_a, hav_b, hfc, hinv, hothers⟩ := hspec
  have hret := erase_subset s.rows i
  constructor
  · intro ha
    rcases ha with ⟨_, w, hw, hx, hr⟩
    exact ⟨wellFormed_withRows s _ hs hret, w, hw, hx, holds_of_rowSubset hret hr⟩
  · rintro ⟨_, w, hw, hx, hr⟩
    have hp : 1 < s.modulus := hs.1
    obtain ⟨val, hval, hmod⟩ := solve_mod s.modulus (lcSum (upd w v 0) target.c) cv cinv
      ((evalLC s.modulus w target.a * evalLC s.modulus w target.b) % s.modulus) hp hinv
      (Nat.mod_lt _ (by omega))
    refine ⟨hs, upd w v val, ⟨?_, ?_⟩, ?_, ?_⟩
    · show (if 0 = v then val else w 0) = 1
      rw [if_neg (fun h => hv0 h.symm)]
      exact hw.1
    · intro j hj
      show (if j = v then val else w j) < s.modulus
      split
      · exact hval
      · exact hw.2 j hj
    · rw [← hx]
      apply List.map_congr_left
      intro a ha
      show (if a = v then val else w a) = w a
      rw [if_neg (fun h : a = v => hvpub (by rw [← h]; exact ha))]
    · intro r hm
      rcases mem_original_or_erased' s.rows i target hti r hm with he | hmem
      · subst he
        unfold rowHolds
        rw [evalLC_upd_avoid _ w v val _ hav_a, evalLC_upd_avoid _ w v val _ hav_b,
          evalLC_eq _ (upd w v val) _, lcSum_upd_single w v cv val _ hfc, hmod]
      · have hot := hothers r hmem
        have ha : ∀ t ∈ r.a, t.wire ≠ v := fun t ht =>
          hot t (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ht))))
        have hb : ∀ t ∈ r.b, t.wire ≠ v := fun t ht =>
          hot t (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ht))))
        have hc : ∀ t ∈ r.c, t.wire ≠ v := fun t ht =>
          hot t (List.mem_append.mpr (Or.inr ht))
        have := hr r hmem
        unfold rowHolds at this ⊢
        rw [evalLC_upd_avoid _ w v val _ ha, evalLC_upd_avoid _ w v val _ hb,
          evalLC_upd_avoid _ w v val _ hc]
        exact this

#print axioms solve_mod
#print axioms lcSum_upd_single
#print axioms dead_output_delete

def deadEx : Shape :=
  ⟨7, 4, [1], [⟨[⟨1, 1⟩], [⟨1, 1⟩], [⟨3, 1⟩]⟩, ⟨[⟨1, 1⟩], [⟨0, 1⟩], [⟨2, 1⟩]⟩]⟩

theorem deadEx_check : deadOutputCheck deadEx 0 3 ⟨[⟨1, 1⟩], [⟨1, 1⟩], [⟨3, 1⟩]⟩ 1 1 = true := by
  decide

theorem deadEx_delete (x : List Nat) :
    accepts deadEx x ↔ accepts (withRows deadEx (deadEx.rows.eraseIdx 0)) x :=
  dead_output_delete deadEx 0 3 1 1 _ (by unfold wellFormed; decide) deadEx_check x

#print axioms deadEx_delete

end MathCan.ZKLean.Compose

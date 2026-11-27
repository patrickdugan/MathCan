import MathCan.ZKLean

/-! ZKL-11: exact quadratic polynomial identities for ordinary R1CS.
Constant multipliers are the degree-two fragment of ideal membership.
Integer coefficient normalization checks the certificate, including the
explicit multiple of the field modulus. No enumeration or primality assumption
is needed for the soundness theorem. Wire zero is the constant one. -/
namespace MathCan.ZKLean.Algebra

open MathCan.ZKLean

def rawLC (w : Assignment) : LC → Nat
  | [] => 0
  | t :: ts => t.coeff * w t.wire + rawLC w ts

theorem fold_rawLC (w : Assignment) (l : LC) (acc : Nat) :
    l.foldl (fun a t => a + t.coeff * w t.wire) acc = acc + rawLC w l := by
  induction l generalizing acc with
  | nil => simp [rawLC]
  | cons t ts ih => simp [rawLC, ih, Nat.add_assoc]

theorem row_raw_dvd (p : Nat) (w : Assignment) (r : Row) :
    rowHolds p w r ↔
      (p : Int) ∣ ((rawLC w r.a : Int) * (rawLC w r.b : Int) - (rawLC w r.c : Int)) := by
  rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  rw [← Int.natCast_mul, ← Int.natCast_emod, ← Int.natCast_emod, Int.ofNat_inj]
  unfold rowHolds evalLC
  simp only [fold_rawLC, Nat.zero_add]
  rw [Nat.mul_mod (rawLC w r.a) (rawLC w r.b) p]

structure QTerm where
  i : Nat
  j : Nat
  coeff : Int
  deriving DecidableEq, Repr

abbrev QPoly := List QTerm

def evalTerm (w : Assignment) (t : QTerm) : Int :=
  t.coeff * ((w t.i : Int) * (w t.j : Int))

def evalQ (w : Assignment) : QPoly → Int
  | [] => 0
  | t :: ts => evalTerm w t + evalQ w ts

theorem eval_append (w : Assignment) (a b : QPoly) :
    evalQ w (a ++ b) = evalQ w a + evalQ w b := by
  induction a with
  | nil => simp [evalQ]
  | cons t ts ih => simp [evalQ, ih, Int.add_assoc]

def mkQ (i j : Nat) (c : Int) : QTerm :=
  if i ≤ j then ⟨i, j, c⟩ else ⟨j, i, c⟩

theorem eval_mkQ (w : Assignment) (i j : Nat) (c : Int) :
    evalTerm w (mkQ i j c) = c * ((w i : Int) * (w j : Int)) := by
  unfold mkQ
  split
  · rfl
  · unfold evalTerm
    ac_rfl

def crossTerm (t : Term) : LC → QPoly
  | [] => []
  | u :: us => mkQ t.wire u.wire ((t.coeff : Int) * (u.coeff : Int)) :: crossTerm t us

def productLC (a b : LC) : QPoly :=
  match a with
  | [] => []
  | t :: ts => crossTerm t b ++ productLC ts b

def linearLC : LC → QPoly
  | [] => []
  | t :: ts => mkQ t.wire 0 (t.coeff : Int) :: linearLC ts

def scale (k : Int) : QPoly → QPoly
  | [] => []
  | t :: ts => { t with coeff := k * t.coeff } :: scale k ts

theorem eval_cross (w : Assignment) (t : Term) (b : LC) :
    evalQ w (crossTerm t b) =
      ((t.coeff : Int) * (w t.wire : Int)) * (rawLC w b : Int) := by
  induction b with
  | nil => simp [crossTerm, rawLC, evalQ]
  | cons u us ih =>
    simp only [crossTerm, evalQ, eval_mkQ, rawLC, Int.natCast_add, Int.natCast_mul, Int.mul_add, ih]
    congr 1 <;> ac_rfl

theorem eval_product (w : Assignment) (a b : LC) :
    evalQ w (productLC a b) = (rawLC w a : Int) * (rawLC w b : Int) := by
  induction a with
  | nil => simp [productLC, evalQ, rawLC]
  | cons t ts ih =>
    simp [productLC, eval_append, eval_cross, ih, rawLC, Int.natCast_add, Int.natCast_mul, Int.add_mul]

theorem eval_linear (w : Assignment) (hz : w 0 = 1) (l : LC) :
    evalQ w (linearLC l) = (rawLC w l : Int) := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    simp [linearLC, evalQ, eval_mkQ, hz, rawLC, ih]

theorem eval_scale (w : Assignment) (k : Int) (q : QPoly) :
    evalQ w (scale k q) = k * evalQ w q := by
  induction q with
  | nil => simp [scale, evalQ]
  | cons t ts ih =>
    simp [scale, evalQ, evalTerm, ih, Int.mul_add, Int.mul_assoc]

def residual (r : Row) : QPoly :=
  productLC r.a r.b ++ scale (-1) (linearLC r.c)

theorem eval_residual (w : Assignment) (hz : w 0 = 1) (r : Row) :
    evalQ w (residual r) =
      (rawLC w r.a : Int) * (rawLC w r.b : Int) - (rawLC w r.c : Int) := by
  rw [residual, eval_append, eval_product, eval_scale, eval_linear w hz]
  omega

theorem row_residual_dvd (p : Nat) (w : Assignment) (hz : w 0 = 1) (r : Row) :
    rowHolds p w r ↔ (p : Int) ∣ evalQ w (residual r) := by
  rw [eval_residual w hz, row_raw_dvd]

/- Canonical coefficient collection. Sorting is used only for completeness
   of the checker; its soundness follows from the evaluation identity. -/
def insertTerm (t : QTerm) : QPoly → QPoly
  | [] => [t]
  | u :: us =>
    if t.i = u.i ∧ t.j = u.j then
      { u with coeff := t.coeff + u.coeff } :: us
    else if t.i < u.i ∨ (t.i = u.i ∧ t.j < u.j) then
      t :: u :: us
    else
      u :: insertTerm t us

theorem eval_insert (w : Assignment) (t : QTerm) (qs : QPoly) :
    evalQ w (insertTerm t qs) = evalTerm w t + evalQ w qs := by
  induction qs with
  | nil => rfl
  | cons u us ih =>
    simp only [insertTerm]
    split
    · rename_i h
      rcases h with ⟨hi, hj⟩
      simp only [evalQ, evalTerm, hi, hj, Int.add_mul]
      omega
    · split
      · rfl
      · simp only [evalQ, ih]
        omega

def sortMerge : QPoly → QPoly
  | [] => []
  | t :: ts => insertTerm t (sortMerge ts)

theorem eval_sortMerge (w : Assignment) (q : QPoly) :
    evalQ w (sortMerge q) = evalQ w q := by
  induction q with
  | nil => rfl
  | cons t ts ih => simp [sortMerge, eval_insert, ih, evalQ]

def dropZeros : QPoly → QPoly
  | [] => []
  | t :: ts => if t.coeff = 0 then dropZeros ts else t :: dropZeros ts

theorem eval_dropZeros (w : Assignment) (q : QPoly) :
    evalQ w (dropZeros q) = evalQ w q := by
  induction q with
  | nil => rfl
  | cons t ts ih =>
    simp only [dropZeros]
    split
    · rename_i h
      simp [ih, evalQ, evalTerm, h]
    · simp [ih, evalQ]

def normalize (q : QPoly) : QPoly := dropZeros (sortMerge q)

theorem eval_normalize (w : Assignment) (q : QPoly) :
    evalQ w (normalize q) = evalQ w q := by
  simp [normalize, eval_dropZeros, eval_sortMerge]

abbrev Weights := List (Int × Row)

def combination : Weights → QPoly
  | [] => []
  | (k, r) :: ts => scale k (residual r) ++ combination ts

theorem combination_dvd (p : Nat) (w : Assignment) (hz : w 0 = 1) (ws : Weights)
    (h : ∀ item ∈ ws, rowHolds p w item.2) :
    (p : Int) ∣ evalQ w (combination ws) := by
  induction ws with
  | nil => simp [combination, evalQ]
  | cons item ts ih =>
    rcases item with ⟨k, r⟩
    have hr : rowHolds p w r := h (k, r) (by simp)
    have ht : (p : Int) ∣ evalQ w (combination ts) :=
      ih (fun item hm => h item (List.mem_cons.mpr (Or.inr hm)))
    rw [combination, eval_append, eval_scale]
    exact Int.dvd_add (Int.dvd_mul_of_dvd_right ((row_residual_dvd p w hz r).mp hr)) ht

def idealCheck (p : Nat) (target : Row) (ws : Weights) (correction : QPoly) : Bool :=
  decide (normalize (residual target) =
    normalize (combination ws ++ scale (p : Int) correction))

theorem ideal_sound (p : Nat) (w : Assignment) (hz : w 0 = 1)
    (target : Row) (ws : Weights) (correction : QPoly)
    (hcheck : idealCheck p target ws correction = true)
    (h : ∀ item ∈ ws, rowHolds p w item.2) :
    rowHolds p w target := by
  have hEq : normalize (residual target) =
      normalize (combination ws ++ scale (p : Int) correction) :=
    of_decide_eq_true hcheck
  have hEval := congrArg (evalQ w) hEq
  simp only [eval_normalize, eval_append, eval_scale] at hEval
  apply (row_residual_dvd p w hz target).mpr
  rw [hEval]
  exact Int.dvd_add (combination_dvd p w hz ws h) ⟨evalQ w correction, rfl⟩

theorem checked_ideal_delete (s : Shape) (rs : List Row)
    (target : Row) (ws : Weights) (correction : QPoly)
    (hs : wellFormed s)
    (hsub : covers rs s.rows = true)
    (hcover : covers s.rows (target :: rs) = true)
    (hweights : covers (ws.map Prod.snd) rs = true)
    (hcheck : idealCheck s.modulus target ws correction = true)
    (x : List Nat) :
    accepts s x ↔ accepts (withRows s rs) x := by
  have hsub' := covers_sound _ _ hsub
  have hcover' := covers_sound _ _ hcover
  have hweights' := covers_sound _ _ hweights
  constructor
  · intro ha
    rcases ha with ⟨_, w, hw, hx, hr⟩
    exact ⟨wellFormed_withRows s rs hs hsub', w, hw, hx, holds_of_rowSubset hsub' hr⟩
  · intro ha
    rcases ha with ⟨_, w, hw, hx, hr⟩
    refine ⟨hs, w, hw, hx, ?_⟩
    intro r hm
    rcases List.mem_cons.mp (hcover' r hm) with he | ht
    · subst r
      apply ideal_sound s.modulus w hw.1 target ws correction hcheck
      intro item hi
      exact hr item.2 (hweights' item.2 (List.mem_map.mpr ⟨item, hi, rfl⟩))
    · exact hr r ht

-- A nonduplicate implication over F7: y = x, z = y entails z = x.
def exampleRows : List Row :=
  [⟨[⟨2,1⟩,⟨1,6⟩], [⟨0,1⟩], []⟩,
   ⟨[⟨3,1⟩,⟨2,6⟩], [⟨0,1⟩], []⟩]
def exampleTarget : Row := ⟨[⟨3,1⟩,⟨1,6⟩], [⟨0,1⟩], []⟩
def exampleWeights : Weights := exampleRows.map (fun r => (1, r))
def exampleCorrection : QPoly := [⟨0,2,-1⟩]

theorem example_check :
    idealCheck 7 exampleTarget exampleWeights exampleCorrection = true := by decide

theorem example_implication (w : Assignment) (hz : w 0 = 1)
    (h : holds 7 w exampleRows) : rowHolds 7 w exampleTarget := by
  apply ideal_sound 7 w hz exampleTarget exampleWeights exampleCorrection example_check
  intro item hm
  rcases List.mem_map.mp hm with ⟨r, hr, he⟩
  subst item
  exact h r hr

#print axioms ideal_sound
#print axioms checked_ideal_delete
#print axioms example_implication

end MathCan.ZKLean.Algebra

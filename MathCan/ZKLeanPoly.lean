import MathCan.ZKLeanAlgebra

/-! ZKL-12: variable-dependent ideal multipliers for ordinary R1CS.
The checker is valid for arbitrary finite monomial lists; search bounds live
outside the kernel. It proves an exact integer identity after substituting w₀=1.
No primality, witness enumeration, or untrusted solver result is required. -/
namespace MathCan.ZKLean.Poly

open MathCan.ZKLean
open MathCan.ZKLean.Algebra (QPoly QTerm evalQ residual row_residual_dvd)

abbrev Mon := List Nat

def evalMon (w : Assignment) : Mon → Int
  | [] => 1
  | i :: is => (w i : Int) * evalMon w is

def stripZero : Mon → Mon
  | [] => []
  | i :: is => if i = 0 then stripZero is else i :: stripZero is

theorem eval_stripZero (w : Assignment) (hz : w 0 = 1) (m : Mon) :
    evalMon w (stripZero m) = evalMon w m := by
  induction m with
  | nil => rfl
  | cons i is ih =>
    simp only [stripZero]
    split
    · rename_i h
      subst i
      simp [evalMon, hz, ih]
    · simp [evalMon, ih]

def insertWire (i : Nat) : Mon → Mon
  | [] => [i]
  | j :: js => if i ≤ j then i :: j :: js else j :: insertWire i js

theorem eval_insertWire (w : Assignment) (i : Nat) (m : Mon) :
    evalMon w (insertWire i m) = (w i : Int) * evalMon w m := by
  induction m with
  | nil => rfl
  | cons j js ih =>
    simp only [insertWire]
    split
    · rfl
    · simp only [evalMon, ih]
      ac_rfl

def mulMon : Mon → Mon → Mon
  | [], b => b
  | i :: is, b => insertWire i (mulMon is b)

theorem eval_mulMon (w : Assignment) (a b : Mon) :
    evalMon w (mulMon a b) = evalMon w a * evalMon w b := by
  induction a with
  | nil => simp [mulMon, evalMon]
  | cons i is ih => simp [mulMon, eval_insertWire, ih, evalMon, Int.mul_assoc]

structure PTerm where
  mon : Mon
  coeff : Int
  deriving DecidableEq, Repr

abbrev PPoly := List PTerm

def evalPTerm (w : Assignment) (t : PTerm) : Int :=
  t.coeff * evalMon w t.mon

def evalP (w : Assignment) : PPoly → Int
  | [] => 0
  | t :: ts => evalPTerm w t + evalP w ts

theorem eval_appendP (w : Assignment) (a b : PPoly) :
    evalP w (a ++ b) = evalP w a + evalP w b := by
  induction a with
  | nil => simp [evalP]
  | cons t ts ih => simp [evalP, ih, Int.add_assoc]

def liftQ : QPoly → PPoly
  | [] => []
  | t :: ts => ⟨stripZero [t.i,t.j], t.coeff⟩ :: liftQ ts

theorem eval_liftQ (w : Assignment) (hz : w 0 = 1) (q : QPoly) :
    evalP w (liftQ q) = evalQ w q := by
  induction q with
  | nil => rfl
  | cons t ts ih =>
    simp [liftQ, evalP, evalPTerm, eval_stripZero w hz, evalMon,
      evalQ, MathCan.ZKLean.Algebra.evalTerm, ih]

def timesMon (k : Int) (m : Mon) : PPoly → PPoly
  | [] => []
  | t :: ts => ⟨mulMon m t.mon, k * t.coeff⟩ :: timesMon k m ts

theorem eval_timesMon (w : Assignment) (k : Int) (m : Mon) (q : PPoly) :
    evalP w (timesMon k m q) = (k * evalMon w m) * evalP w q := by
  induction q with
  | nil => simp [timesMon, evalP]
  | cons t ts ih =>
    simp only [timesMon, evalP, evalPTerm, eval_mulMon, ih, Int.mul_add]
    congr 1 <;> ac_rfl

def insertP (t : PTerm) : PPoly → PPoly
  | [] => [t]
  | u :: us =>
    if t.mon = u.mon then { u with coeff := t.coeff + u.coeff } :: us
    else u :: insertP t us

theorem eval_insertP (w : Assignment) (t : PTerm) (q : PPoly) :
    evalP w (insertP t q) = evalPTerm w t + evalP w q := by
  induction q with
  | nil => rfl
  | cons u us ih =>
    simp only [insertP]
    split
    · rename_i h
      simp only [evalP, evalPTerm, h, Int.add_mul]
      omega
    · simp only [evalP, ih]
      omega

def collect : PPoly → PPoly
  | [] => []
  | t :: ts => insertP t (collect ts)

theorem eval_collect (w : Assignment) (q : PPoly) :
    evalP w (collect q) = evalP w q := by
  induction q with
  | nil => rfl
  | cons t ts ih => simp [collect, eval_insertP, ih, evalP]

def dropZeroP : PPoly → PPoly
  | [] => []
  | t :: ts => if t.coeff = 0 then dropZeroP ts else t :: dropZeroP ts

theorem eval_dropZeroP (w : Assignment) (q : PPoly) :
    evalP w (dropZeroP q) = evalP w q := by
  induction q with
  | nil => rfl
  | cons t ts ih =>
    simp only [dropZeroP]
    split
    · rename_i h
      simp [ih, evalP, evalPTerm, h]
    · simp [ih, evalP]

def normalizeP (q : PPoly) : PPoly := dropZeroP (collect q)

theorem eval_normalizeP (w : Assignment) (q : PPoly) :
    evalP w (normalizeP q) = evalP w q := by
  simp [normalizeP, eval_dropZeroP, eval_collect]

structure Multiplier where
  coeff : Int
  mon : Mon
  row : Row

def combinationP : List Multiplier → PPoly
  | [] => []
  | t :: ts => timesMon t.coeff t.mon (liftQ (residual t.row)) ++ combinationP ts

theorem combinationP_dvd (p : Nat) (w : Assignment) (hz : w 0 = 1)
    (ws : List Multiplier) (h : ∀ t ∈ ws, rowHolds p w t.row) :
    (p : Int) ∣ evalP w (combinationP ws) := by
  induction ws with
  | nil => simp [combinationP, evalP]
  | cons t ts ih =>
    have hr : rowHolds p w t.row := h t (by simp)
    have ht : (p : Int) ∣ evalP w (combinationP ts) :=
      ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))
    rw [combinationP, eval_appendP, eval_timesMon, eval_liftQ w hz]
    exact Int.dvd_add (Int.dvd_mul_of_dvd_right ((row_residual_dvd p w hz t.row).mp hr)) ht

def rhs (p : Nat) (ws : List Multiplier) (correction : PPoly) : PPoly :=
  combinationP ws ++ timesMon (p : Int) [] correction

def polyCheck (p : Nat) (target : Row) (ws : List Multiplier) (correction : PPoly) : Bool :=
  decide (normalizeP (liftQ (residual target) ++ timesMon (-1) [] (rhs p ws correction)) = [])

theorem poly_sound (p : Nat) (w : Assignment) (hz : w 0 = 1)
    (target : Row) (ws : List Multiplier) (correction : PPoly)
    (hc : polyCheck p target ws correction = true)
    (h : ∀ t ∈ ws, rowHolds p w t.row) :
    rowHolds p w target := by
  have he : normalizeP (liftQ (residual target) ++ timesMon (-1) [] (rhs p ws correction)) = [] :=
    of_decide_eq_true hc
  have hv := congrArg (evalP w) he
  simp only [eval_normalizeP, eval_appendP, eval_timesMon, evalMon, Int.mul_one,
    eval_liftQ w hz, evalP] at hv
  have eqv : evalQ w (residual target) = evalP w (rhs p ws correction) := by omega
  apply (row_residual_dvd p w hz target).mpr
  rw [eqv, rhs, eval_appendP, eval_timesMon]
  simp only [evalMon, Int.mul_one]
  exact Int.dvd_add (combinationP_dvd p w hz ws h) ⟨evalP w correction, rfl⟩

theorem checked_poly_delete (s : Shape) (rs : List Row)
    (target : Row) (ws : List Multiplier) (correction : PPoly)
    (hs : wellFormed s)
    (hsub : covers rs s.rows = true)
    (hcover : covers s.rows (target :: rs) = true)
    (hweights : covers (ws.map Multiplier.row) rs = true)
    (hc : polyCheck s.modulus target ws correction = true)
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
      apply poly_sound s.modulus w hw.1 target ws correction hc
      intro item hi
      exact hr item.row (hweights' item.row (List.mem_map.mpr ⟨item, hi, rfl⟩))
    · exact hr r ht

def linearZero : Row := ⟨[⟨1,1⟩], [⟨0,1⟩], []⟩
def productZero : Row := ⟨[⟨1,1⟩], [⟨2,1⟩], []⟩
def degreeOne : List Multiplier := [⟨1,[2],linearZero⟩]

theorem degree_one_check : polyCheck 7 productZero degreeOne [] = true := by decide
theorem degree_one_sound (w : Assignment) (hz : w 0 = 1)
    (h : rowHolds 7 w linearZero) : rowHolds 7 w productZero := by
  apply poly_sound 7 w hz productZero degreeOne [] degree_one_check
  intro t ht
  have he : t = ⟨1,[2],linearZero⟩ := List.mem_singleton.mp ht
  subst t
  exact h

-- y²*x² - (xy+z)*(xy-z) = z² (wire 1=x, 2=y, 3=z).
def xyIsZ : Row := ⟨[⟨1,1⟩],[⟨2,1⟩],[⟨3,1⟩]⟩
def xSquaredZero : Row := ⟨[⟨1,1⟩],[⟨1,1⟩],[]⟩
def zSquaredZero : Row := ⟨[⟨3,1⟩],[⟨3,1⟩],[]⟩
def degreeTwo : List Multiplier :=
  [⟨1,[2,2],xSquaredZero⟩, ⟨-1,[1,2],xyIsZ⟩, ⟨-1,[3],xyIsZ⟩]

theorem degree_two_check : polyCheck 7 zSquaredZero degreeTwo [] = true := by decide
theorem degree_two_sound (w : Assignment) (hz : w 0 = 1)
    (h : holds 7 w [xyIsZ,xSquaredZero]) : rowHolds 7 w zSquaredZero := by
  apply poly_sound 7 w hz zSquaredZero degreeTwo [] degree_two_check
  intro t ht
  rcases List.mem_cons.mp ht with he | ht
  · subst t
    exact h _ (by simp)
  · rcases List.mem_cons.mp ht with he | ht
    · subst t
      exact h _ (by simp)
    · have he := List.mem_singleton.mp ht
      subst t
      exact h _ (by simp)

#print axioms poly_sound
#print axioms checked_poly_delete
#print axioms degree_one_sound
#print axioms degree_two_sound

end MathCan.ZKLean.Poly

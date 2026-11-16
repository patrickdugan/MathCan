import MathCan.SpatialClipped

/-!
Exact base-4 payloads with a trailing digit-one sentinel. The digit reader
and clipped suffix are the affine/ReLU formulas in spatial_circuit.py.
The sentinel is retained after the final payload bit; it is never decoded
as a payload. Scalars use the standard ordered-field laws of Lean core.
-/
namespace MathCan.SentinelDecoder
open Std Lean.Grind MathCan.SpatialScalar
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast Ring.intCast

def bit : Bool → R
  | false => 0
  | true => 1

def word : List Bool → R
  | [] => 1/4
  | b :: tail => (1 + bit b + word tail)/4

def readBit (z : R) : R := 4*(relu (4*z-7/4) - relu (4*z-2))
def nextWord (z : R) : R := clip 1 (4*z-1-readBit z)

theorem bit_binary (b : Bool) : bit (R := R) b = 0 ∨ bit (R := R) b = 1 := by
  cases b <;> simp [bit]

/-- A uniform suffix invariant, including the empty payload's sentinel. -/
theorem word_range (bits : List Bool) : 1/4 ≤ word (R := R) bits ∧ word (R := R) bits ≤ 2/3 := by
  induction bits with
  | nil => simp only [word]; constructor <;> grind
  | cons b tail ih => cases b <;> simp only [word, bit] <;> constructor <;> grind

theorem word_nonnegative (bits : List Bool) : 0 ≤ word (R := R) bits := by
  have := word_range (R := R) bits
  grind

theorem read_bit_zero (tail : R) (ht : 1/4 ≤ tail ∧ tail ≤ 2/3) :
    readBit ((1+tail)/4) = 0 := by
  unfold readBit relu
  repeat' split <;> grind

theorem read_bit_one (tail : R) (ht : 1/4 ≤ tail ∧ tail ≤ 2/3) :
    readBit ((2+tail)/4) = 1 := by
  unfold readBit relu
  repeat' split <;> grind

/-- The reader returns exactly the leading payload bit. -/
theorem read_word_cons (b : Bool) (tail : List Bool) :
    readBit (word (R := R) (b::tail)) = bit b := by
  cases b
  · simpa only [word,bit,AddCommMonoid.add_zero] using
      read_bit_zero (R := R) (word tail) (word_range tail)
  · change readBit ((1+1+word tail)/4) = 1
    have h : (1:R)+1 = 2 := by grind
    rw [h]
    exact read_bit_one (R := R) (word tail) (word_range tail)

/-- The clipped update is exactly the encoded suffix, including its sentinel. -/
theorem next_word_cons (b : Bool) (tail : List Bool) :
    nextWord (word (R := R) (b::tail)) = word tail := by
  unfold nextWord
  rw [read_word_cons]
  have hraw : 4*word (R := R) (b::tail)-1-bit b = word tail := by
    rw [word]
    grind
  rw [hraw]
  apply clip_identity
  have := word_range (R := R) tail
  constructor <;> grind

def decode : Nat → R → List R
  | 0, _ => []
  | n+1, z => readBit z :: decode n (nextWord z)

def advance : Nat → R → R
  | 0, z => z
  | n+1, z => advance n (nextWord z)

/-- Every finite payload is recovered; no assertion is made about a sentinel read. -/
theorem decode_word (bits : List Bool) :
    decode bits.length (word (R := R) bits) = bits.map (bit (R := R)) := by
  induction bits with
  | nil => rfl
  | cons b tail ih =>
    simp only [List.length_cons, decode, read_word_cons, next_word_cons, List.map_cons, ih]

theorem advance_word (bits : List Bool) :
    advance bits.length (word (R := R) bits) = 1/4 := by
  induction bits with
  | nil => rfl
  | cons b tail ih => simpa only [List.length_cons,advance,next_word_cons] using ih

theorem next_word_range (z : R) : 0 ≤ nextWord z ∧ nextWord z ≤ 1 := by
  exact clip_range 1 _ (by grind)

/-- The digit reader saturates between zero and one for arbitrary scalar input. -/
theorem read_bit_range (z : R) : 0 ≤ readBit z ∧ readBit z ≤ 1 := by
  unfold readBit relu
  repeat' split <;> constructor <;> grind

theorem decode_prefix (headBits tail : List Bool) :
    decode headBits.length (word (R := R) (headBits++tail)) = headBits.map (bit (R := R)) := by
  induction headBits with
  | nil => rfl
  | cons b headBits ih =>
    simp only [List.cons_append,List.length_cons,decode,read_word_cons,next_word_cons,List.map_cons,ih]

theorem advance_prefix (headBits tail : List Bool) :
    advance headBits.length (word (R := R) (headBits++tail)) = word tail := by
  induction headBits with
  | nil => rfl
  | cons b headBits ih => simpa only [List.cons_append,List.length_cons,advance,next_word_cons] using ih

/-- A closed 1/48 input margin suffices at each valid payload read. -/
theorem read_word_perturbed (b : Bool) (tail : List Bool) (e : R)
    (he : -1/48 ≤ e ∧ e ≤ 1/48) :
    readBit (word (b::tail)+e) = bit (R := R) b := by
  have ht := word_range (R := R) tail
  cases b <;> unfold word bit readBit relu <;> repeat' split <;> grind

/-- Within the digit margin, the state error is amplified by exactly four. -/
theorem next_word_perturbed (b : Bool) (tail : List Bool) (e : R)
    (he : -1/48 ≤ e ∧ e ≤ 1/48) :
    nextWord (word (b::tail)+e) = word (R := R) tail+4*e := by
  unfold nextWord
  rw [read_word_perturbed b tail e he]
  have hraw : 4*(word (R := R) (b::tail)+e)-1-bit b = word tail+4*e := by
    rw [word]
    grind
  rw [hraw]
  apply clip_identity
  have ht := word_range (R := R) tail
  constructor <;> grind

def noiseBudget : Nat → R
  | 0 => 1/48
  | n+1 => noiseBudget n/4

theorem noise_budget_range (n : Nat) :
    0 < noiseBudget (R := R) n ∧ noiseBudget (R := R) n ≤ 1/48 := by
  induction n with
  | zero => simp only [noiseBudget]; constructor <;> grind
  | succ n ih => simp only [noiseBudget]; constructor <;> grind

theorem noise_budget_step (n : Nat) (e : R)
    (he : -noiseBudget (R := R) (n+1) ≤ e ∧ e ≤ noiseBudget (R := R) (n+1)) :
    -noiseBudget (R := R) n ≤ 4*e ∧ 4*e ≤ noiseBudget (R := R) n := by
  simp only [noiseBudget] at he
  constructor <;> grind

/-- All payload bits survive a length-dependent two-sided input perturbation. -/
theorem decode_word_robust (bits : List Bool) (e : R)
    (he : -noiseBudget (R := R) bits.length ≤ e ∧ e ≤ noiseBudget (R := R) bits.length) :
    decode bits.length (word bits+e) = bits.map (bit (R := R)) := by
  induction bits generalizing e with
  | nil => rfl
  | cons b tail ih =>
    have hb := noise_budget_range (R := R) (b::tail).length
    have hs : -1/48 ≤ e ∧ e ≤ 1/48 := by constructor <;> grind
    simp only [List.length_cons,decode]
    rw [read_word_perturbed b tail e hs,next_word_perturbed b tail e hs]
    exact congrArg (List.cons (bit b)) (ih (4*e) (noise_budget_step tail.length e he))

def noiseAdvance : Nat → R → R
  | 0,e => e
  | n+1,e => noiseAdvance n (4*e)

theorem noise_advance_eq (n : Nat) (e : R) : noiseAdvance n e = (4:R)^n*e := by
  induction n generalizing e with
  | zero => simp only [noiseAdvance,Semiring.pow_zero,Semiring.one_mul]
  | succ n ih => rw [noiseAdvance,ih,Semiring.pow_succ]; grind

theorem advance_word_robust (bits : List Bool) (e : R)
    (he : -noiseBudget (R := R) bits.length ≤ e ∧ e ≤ noiseBudget (R := R) bits.length) :
    advance bits.length (word bits+e) = 1/4+noiseAdvance bits.length e := by
  induction bits generalizing e with
  | nil => rfl
  | cons b tail ih =>
    have hb := noise_budget_range (R := R) (b::tail).length
    have hs : -1/48 ≤ e ∧ e ≤ 1/48 := by constructor <;> grind
    simp only [List.length_cons,advance,noiseAdvance]
    rw [next_word_perturbed b tail e hs]
    exact ih (4*e) (noise_budget_step tail.length e he)

def payloadNumerator : List Bool → Nat
  | [] => 1
  | b::tail => (if b then 2 else 1)*4^(tail.length+1)+payloadNumerator tail

/-- The stored code has an integer numerator over 4^(S+1). -/
theorem word_scaled_integer (bits : List Bool) :
    word (R := R) bits*(4:R)^(bits.length+1) = (payloadNumerator bits:R) := by
  induction bits with
  | nil => simp only [word,List.length_nil,Semiring.pow_one,payloadNumerator,Semiring.natCast_one]; grind
  | cons b tail ih =>
    cases b <;> simp only [word,bit,List.length_cons,payloadNumerator,Bool.false_eq_true,if_false,if_true,
      Semiring.natCast_add,Semiring.natCast_mul,Semiring.natCast_pow,
      Semiring.natCast_eq_ofNat (α := R) 1,Semiring.natCast_eq_ofNat (α := R) 2,
      Semiring.natCast_eq_ofNat (α := R) 4] <;> rw [Semiring.pow_succ] <;> grind

theorem four_pow_binary (n : Nat) : (4:R)^n = (2:R)^(2*n) := by
  induction n with
  | zero => simp only [Nat.mul_zero,Semiring.pow_zero]
  | succ n ih =>
    rw [Nat.mul_succ,Semiring.pow_succ,Semiring.pow_add,← ih,Semiring.pow_two]
    grind

/-- Exactly 2(S+1) binary fractional slots suffice for the stored word. -/
theorem word_binary_precision (bits : List Bool) :
    word (R := R) bits*(2:R)^(2*(bits.length+1)) = (payloadNumerator bits:R) := by
  rw [← four_pow_binary,word_scaled_integer]

theorem payload_numerator_bound (bits : List Bool) :
    payloadNumerator bits < 4^(bits.length+1) := by
  induction bits with
  | nil => decide
  | cons b tail ih =>
    have hp : 0 < 4^(tail.length+1) := Nat.pow_pos (by omega)
    cases b <;> simp only [payloadNumerator,List.length_cons,Nat.pow_succ,
      Bool.false_eq_true,if_false,if_true] <;> omega

theorem decode_take (n m : Nat) (z : R) :
    decode n z = (decode (n+m) z).take n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.succ_add,decode,List.take_succ_cons]
    exact congrArg (List.cons (readBit z)) (ih (nextWord z))

theorem decode_prefix_robust (headBits tail : List Bool) (e : R)
    (he : -noiseBudget (R := R) (headBits++tail).length ≤ e ∧
      e ≤ noiseBudget (R := R) (headBits++tail).length) :
    decode headBits.length (word (headBits++tail)+e) = headBits.map (bit (R := R)) := by
  rw [decode_take headBits.length tail.length]
  have h := decode_word_robust (R := R) (headBits++tail) e he
  rw [List.length_append] at h
  rw [h,List.map_append]
  have hl : headBits.length = (headBits.map (bit (R := R))).length := by simp
  rw [hl,List.take_left]

theorem noise_budget_transport (n m : Nat) (e : R)
    (he : -noiseBudget (R := R) (n+m) ≤ e ∧ e ≤ noiseBudget (R := R) (n+m)) :
    -noiseBudget (R := R) m ≤ noiseAdvance n e ∧ noiseAdvance n e ≤ noiseBudget (R := R) m := by
  induction n generalizing e with
  | zero => simpa only [Nat.zero_add,noiseAdvance] using he
  | succ n ih =>
    rw [noiseAdvance]
    apply ih (4*e)
    apply noise_budget_step (n+m) e
    simpa only [Nat.succ_add] using he

theorem advance_prefix_robust (headBits tail : List Bool) (e : R)
    (he : -noiseBudget (R := R) (headBits++tail).length ≤ e ∧
      e ≤ noiseBudget (R := R) (headBits++tail).length) :
    advance headBits.length (word (headBits++tail)+e) = word (R := R) tail+noiseAdvance headBits.length e := by
  induction headBits generalizing e with
  | nil => rfl
  | cons b headBits ih =>
    have hb := noise_budget_range (R := R) ((b::headBits)++tail).length
    have hs : -1/48 ≤ e ∧ e ≤ 1/48 := by constructor <;> grind
    simp only [List.cons_append,List.length_cons,advance,noiseAdvance]
    rw [next_word_perturbed b (headBits++tail) e hs]
    apply ih (4*e)
    apply noise_budget_step (headBits++tail).length e
    simpa only [List.cons_append,List.length_cons] using he

end MathCan.SentinelDecoder

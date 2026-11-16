import MathCan.DecodedJetCapture

/-! Finite Hamming selectors and little-endian amplitude words. The selector
uses the same affine score and ReLU as the displacement circuit. -/
namespace MathCan.HammingSelector
open Std Lean.Grind MathCan.SpatialScalar MathCan.SentinelDecoder MathCan.DecodedJetCapture
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast Ring.intCast

def hamming : List Bool → List Bool → Nat
  | [],ys => ys.length
  | xs,[] => xs.length
  | b::bs,c::cs => (if b=c then 0 else 1)+hamming bs cs

def distance : List Bool → List R → R
  | [],_ => 0
  | b::bs,[] => (if b then 1 else 0)+distance bs []
  | b::bs,x::xs => (if b then 1-x else x)+distance bs xs

def selector (pattern : List Bool) (inputs : List R) : R := relu (1-distance pattern inputs)

theorem hamming_self (bits : List Bool) : hamming bits bits = 0 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [hamming,ih]

theorem hamming_zero_iff (xs ys : List Bool) : hamming xs ys = 0 ↔ xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [hamming]
  | cons b bs ih =>
    cases ys with
    | nil => simp [hamming]
    | cons c cs => by_cases h:b=c <;> simp [hamming,h,ih]

theorem distance_bits (pattern bits : List Bool) (hlen : pattern.length=bits.length) :
    distance pattern (bits.map (bit (R := R))) = (hamming pattern bits:R) := by
  induction pattern generalizing bits with
  | nil => cases bits <;> simp_all [distance,hamming,Semiring.natCast_zero]
  | cons b bs ih =>
    cases bits with
    | nil => simp at hlen
    | cons c cs =>
      have ht : bs.length=cs.length := by simpa using hlen
      cases b <;> cases c <;> simp [distance,hamming,bit,ih cs ht,
        Semiring.natCast_add,Semiring.natCast_zero,Semiring.natCast_one] <;> grind

theorem selector_bits (pattern bits : List Bool) (hlen : pattern.length=bits.length) :
    selector pattern (bits.map (bit (R := R))) = if pattern=bits then 1 else 0 := by
  unfold selector
  rw [distance_bits pattern bits hlen]
  by_cases h:pattern=bits
  · subst bits
    rw [hamming_self,Semiring.natCast_zero,if_pos rfl]
    unfold relu
    split <;> grind
  · rw [if_neg h]
    have hn : 1 ≤ hamming pattern bits := by
      have hh : hamming pattern bits ≠ 0 := fun hz => h ((hamming_zero_iff pattern bits).mp hz)
      omega
    have hr := OrderedRing.natCast_le_natCast_of_le (R := R) 1 _ hn
    rw [Semiring.natCast_one] at hr
    exact relu_of_nonpos _ (by grind)

def digits : Nat → Nat → List Bool
  | 0,_ => []
  | p+1,q => decide (q%2=1) :: digits p (q/2)

theorem digits_length (p q : Nat) : (digits p q).length=p := by
  induction p generalizing q with
  | zero => rfl
  | succ p ih => simp [digits,ih]

theorem digits_value (p q : Nat) (hq : q < 2^p) : unsignedNat (digits p q)=q := by
  induction p generalizing q with
  | zero =>
    have h:q=0 := by simpa using hq
    subst q
    rfl
  | succ p ih =>
    have hmod := Nat.mod_lt q (by omega : 0<2)
    have hdecomp := Nat.mod_add_div q 2
    have htail : q/2 < 2^p := by rw [Nat.pow_succ] at hq; omega
    simp only [digits,unsignedNat,ih _ htail]
    by_cases h:q%2=1 <;> simp [h] <;> omega

theorem digits_injective (p q r : Nat) (hq : q<2^p) (hr : r<2^p)
    (h : digits p q=digits p r) : q=r := by
  have hh := congrArg unsignedNat h
  rw [digits_value p q hq,digits_value p r hr] at hh
  exact hh

def amplitude (p q : Nat) (inputs : List R) : R := selector (digits p q) inputs

theorem amplitude_one_hot (p q r : Nat) (hq : q<2^p) (hr : r<2^p) :
    amplitude p q ((digits p r).map (bit (R := R))) = if q=r then 1 else 0 := by
  unfold amplitude
  rw [selector_bits _ _ (by simp [digits_length])]
  by_cases h:q=r
  · subst r; simp
  · rw [if_neg h,if_neg (fun he => h (digits_injective p q r hq hr he))]

theorem power_two_width (r : Nat) : 2^r < 2^(r+1) := by
  have h:0<2^r := Nat.pow_pos (by omega)
  rw [Nat.pow_succ]
  omega

def chooseScalar (D p : Nat) (C : R) (inputs : List R) (values : Nat → R) : R :=
  sum (D+1) (fun q => gate C (amplitude p q inputs) (values q))

theorem choose_scalar_exact (D p r : Nat) (hwidth : D<2^p) (hr : r≤D)
    (C : R) (values : Nat → R) (bounds : ∀ q, q≤D → -C≤values q ∧ values q≤C) :
    chooseScalar D p C ((digits p r).map bit) values = values r := by
  unfold chooseScalar
  calc
    _ = sum (D+1) (fun q => if q=r then values r else 0) := by
      apply sum_congr
      intro q hq
      rw [amplitude_one_hot p q r (by omega) (by omega)]
      by_cases h:q=r
      · subst q; rw [if_pos rfl,gate_one C _ (bounds r hr)]
        simp
      · rw [if_neg h,gate_zero]
        simp [h]
    _ = values r := sum_single _ _ (by omega) _

theorem choose_vector_exact (D p r J : Nat) (hwidth : D<2^p) (hr : r≤D)
    (C : R) (values : Nat → Fin J → R)
    (bounds : ∀ q, q≤D → ∀ beta, -C≤values q beta ∧ values q beta≤C) :
    (fun beta => chooseScalar D p C ((digits p r).map bit) (fun q=>values q beta)) = values r := by
  funext beta
  exact choose_scalar_exact D p r hwidth hr C _ (fun q hq=>bounds q hq beta)

end MathCan.HammingSelector

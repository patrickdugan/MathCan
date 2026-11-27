import MathCan.DETFACT15Stream
import MathCan.DETFACT16Saturation

/-!
DETFACT-17: compose the certified saturation roster with the odd-only
stream and two-adic split probes. Roster validity, coverage and native
implementation refinement remain explicit external obligations.
-/
namespace MathCan.DETFACT17OddSplit

open MathCan.DETFACT16Saturation
open MathCan.DETFACT15Stream

def Odd (n : Nat) : Prop := n % 2 = 1

theorem odd_mul (a b : Nat) (ha : Odd a) (hb : Odd b) : Odd (a*b) := by
  unfold Odd at *
  calc
    (a*b) % 2 = ((a%2)*b)%2 := (reduce_left a b 2).symm
    _ = ((a%2)*(b%2))%2 := (reduce_right (a%2) b 2).symm
    _ = 1 := by rw [ha,hb]

theorem odd_pow (p e : Nat) (hp : Odd p) : Odd (p^e) := by
  induction e with
  | zero => decide
  | succ e ih => rw [Nat.pow_succ]; exact odd_mul _ _ ih hp

theorem prime_two : PrimeLike 2 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have hpos := Nat.pos_of_dvd_of_pos hd (show 0 < 2 by decide)
  have hle := Nat.le_of_dvd (show 0 < 2 by decide) hd
  omega

theorem prime_other_odd (p : Nat) (hp : PrimeLike p)
    (hne : p ≠ 2) : Odd p := by
  unfold Odd
  have hlt : p % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : p % 2 = 0
  · have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases hp.2 2 hd with hbad | heq
    · omega
    · exact False.elim (hne heq.symm)
  · omega

/-- Uniqueness of a maximal exponent for any base > 1. -/
theorem maximal_exponent_unique (p K a b : Nat) (hp : 1 < p)
    (ha : p^a ≤ K) (han : K < p^(a+1))
    (hb : p^b ≤ K) (hbn : K < p^(b+1)) : a = b := by
  by_cases h₁ : a < b
  · have hh := Nat.pow_le_pow_of_le hp (show a+1 ≤ b by omega)
    omega
  · by_cases h₂ : b < a
    · have hh := Nat.pow_le_pow_of_le hp (show b+1 ≤ a by omega)
      omega
    · omega

theorem factor_two_exists (m : Nat) (hm : 0 < m) :
    ∃ s u : Nat, m = 2^s*u ∧ Odd u := by
  obtain ⟨s,u,hu,heq,hn⟩ := strip_power 2 m (by decide) hm
  refine ⟨s,u,heq,?_⟩
  unfold Odd
  have hlt : u % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : u % 2 = 0
  · exact False.elim (hn (Nat.dvd_of_mod_eq_zero h))
  · omega

/-- A higher exponent of two cannot occur in an odd cofactor. -/
theorem two_factor_strict_impossible (s t u v : Nat)
    (hu : Odd u) (hst : s < t) (heq : 2^s*u = 2^t*v) : False := by
  have ht : t = s + (t-s) := by omega
  have heq' : 2^s*u = 2^s*(2^(t-s)*v) := by
    calc
      2^s*u = 2^t*v := heq
      _ = 2^(s+(t-s))*v := by rw [← ht]
      _ = 2^s*(2^(t-s)*v) := by rw [Nat.pow_add, Nat.mul_assoc]
  have hc := Nat.mul_left_cancel (Nat.two_pow_pos s) heq'
  have hd : 2 ∣ u := by
    rw [hc]
    exact Nat.dvd_mul_right_of_dvd
      (Nat.dvd_of_pow_dvd (show 1 ≤ t-s by omega)
        (Nat.dvd_refl (2^(t-s)))) v
  have hz := Nat.mod_eq_zero_of_dvd hd
  unfold Odd at hu
  omega

theorem factor_two_unique (s t u v : Nat)
    (hu : Odd u) (hv : Odd v) (heq : 2^s*u = 2^t*v) :
    s = t ∧ u = v := by
  have hst : s = t := by
    by_cases h : s < t
    · exact False.elim (two_factor_strict_impossible s t u v hu h heq)
    · by_cases h' : t < s
      · exact False.elim (two_factor_strict_impossible t s v u hv h' heq.symm)
      · omega
  refine ⟨hst, ?_⟩
  rw [← hst] at heq
  exact Nat.mul_left_cancel (Nat.two_pow_pos s) heq

def twoExponent : List Entry → Nat
  | [] => 0
  | e :: es => if e.1 = 2 then e.2 + twoExponent es else twoExponent es

def oddFactors : List Entry → List Nat
  | [] => []
  | e :: es => if e.1 = 2 then oddFactors es else entryPower e :: oddFactors es

theorem roster_split_product (es : List Entry) :
    rosterProduct es = 2^(twoExponent es)*exponentProduct (oddFactors es) := by
  induction es with
  | nil => simp [rosterProduct,twoExponent,oddFactors,exponentProduct]
  | cons e es ih =>
    by_cases h : e.1 = 2
    · simp only [rosterProduct,twoExponent,oddFactors,if_pos h,entryPower, h]
      rw [ih, Nat.pow_add]
      ac_rfl
    · simp only [rosterProduct,twoExponent,oddFactors,if_neg h,exponentProduct]
      rw [ih]
      ac_rfl

theorem odd_factors_product (K : Nat) (es : List Entry)
    (hv : ∀ e : Entry, e ∈ es → ValidEntry K e) :
    Odd (exponentProduct (oddFactors es)) := by
  induction es with
  | nil => decide
  | cons e es ih =>
    have ht := ih (fun f hf => hv f (by simp [hf]))
    by_cases h : e.1 = 2
    · simpa only [oddFactors,if_pos h] using ht
    · have ho : Odd (entryPower e) :=
        odd_pow e.1 e.2 (prime_other_odd e.1 (hv e (by simp)).1 h)
      simpa only [oddFactors,if_neg h,exponentProduct] using
        odd_mul _ _ ho ht

theorem two_exponent_absent (es : List Entry)
    (h : ∀ e : Entry, e ∈ es → e.1 ≠ 2) : twoExponent es = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun f hf => h f (by simp [hf]))
    simp only [twoExponent,if_neg he,ht]

theorem two_exponent_member (es : List Entry) (e : Entry)
    (hu : UniqueLabels es) (hm : e ∈ es) (he : e.1 = 2) :
    twoExponent es = e.2 := by
  induction es with
  | nil => simp at hm
  | cons f fs ih =>
    have hu' : (∀ g : Entry, g ∈ fs → f.1 ≠ g.1) ∧ UniqueLabels fs := hu
    rcases List.mem_cons.mp hm with heq | ht
    · subst e
      have hz : twoExponent fs = 0 :=
        two_exponent_absent fs (fun g hg hg2 =>
          hu'.1 g hg (he.trans hg2.symm))
      simp only [twoExponent,if_pos he,hz,Nat.add_zero]
    · have hne : f.1 ≠ 2 := fun hf => hu'.1 e ht (hf.trans he.symm)
      simp only [twoExponent,if_neg hne]
      exact ih hu'.2 ht

theorem two_exponent_bounds (K : Nat) (es : List Entry) (hK : 1 ≤ K)
    (hv : ∀ e : Entry, e ∈ es → ValidEntry K e)
    (hu : UniqueLabels es) (hc : CompleteLabels K es) :
    2^(twoExponent es) ≤ K ∧ K < 2^(twoExponent es+1) := by
  by_cases h : 2 ≤ K
  · obtain ⟨e,hm,he⟩ := hc 2 prime_two h
    have ht := two_exponent_member es e hu hm he
    have hb := (hv e hm).2.2
    unfold entryPower at hb
    rw [he] at hb
    rw [ht]
    exact hb
  · have hz : twoExponent es = 0 := by
      apply two_exponent_absent
      intro e hm he
      have ev := hv e hm
      have hpow : 1 < e.1^e.2 := Nat.one_lt_pow (by have := ev.2.1; omega) ev.1.1
      have hle := ev.2.2.1
      unfold entryPower at hle
      omega
    rw [hz]
    exact ⟨by simpa using hK, by simpa using (show K < 2 by omega)⟩

def splitCount (s : Nat) (es : List Entry) : Nat := 1+s+twoExponent es

def oddStream (u : Nat) (es : List Entry) : List Nat := u :: oddFactors es

/-- The complete saturated exponent has exactly the declared odd stream
and two-adic count, assuming a valid, unique and complete roster. -/
theorem saturated_decomposition (K M s u : Nat) (es : List Entry)
    (hM : M = 2^s*u) (ho : Odd u)
    (hv : ∀ e : Entry, e ∈ es → ValidEntry K e)
    (hu : UniqueLabels es) (hc : CompleteLabels K es) :
    2*M*intervalLCM K =
      2^(splitCount s es)*exponentProduct (oddStream u es) ∧
    Odd (exponentProduct (oddStream u es)) := by
  constructor
  · rw [← certified_roster_eq_interval_lcm K es hv hu hc, hM, roster_split_product]
    simp only [splitCount,oddStream,exponentProduct]
    rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
    ac_rfl
  · exact odd_mul _ _ ho (odd_factors_product K es hv)

theorem saturated_odd_quotient (K M s u : Nat) (es : List Entry)
    (hM : M = 2^s*u) (ho : Odd u)
    (hv : ∀ e : Entry, e ∈ es → ValidEntry K e)
    (hu : UniqueLabels es) (hc : CompleteLabels K es) :
    (2*M*intervalLCM K) / 2^(splitCount s es) =
      exponentProduct (oddStream u es) := by
  rw [(saturated_decomposition K M s u es hM ho hv hu hc).1]
  exact Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)

/-- Pointwise native split specification with the explicit saturated
integer exponent replaced by the certified odd stream. -/
theorem saturated_stream_split_probe (K M s u n a j : Nat) (es : List Entry)
    (hM : M = 2^s*u) (ho : Odd u)
    (hv : ∀ e : Entry, e ∈ es → ValidEntry K e)
    (hu : UniqueLabels es) (hc : CompleteLabels K es) :
    splitProbe n (execute n a (oddStream u es)) j =
      Nat.gcd (gcdInput
        (a ^ (((2*M*intervalLCM K) / 2^(splitCount s es)) * 2^j) % n)) n := by
  rw [saturated_odd_quotient K M s u es hM ho hv hu hc]
  exact split_probe_eq n a j (oddStream u es)

#print axioms maximal_exponent_unique
#print axioms factor_two_exists
#print axioms factor_two_unique
#print axioms two_exponent_bounds
#print axioms saturated_decomposition
#print axioms saturated_odd_quotient
#print axioms saturated_stream_split_probe
end MathCan.DETFACT17OddSplit

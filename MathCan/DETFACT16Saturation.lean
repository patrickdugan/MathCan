import Lean

/-!
DETFACT-16: a complete, unique roster of maximal prime powers
certifies the interval lcm. Elementary number theory in core Lean.
The concrete sieve implementation and the upstream relation producer
are outside this model.
-/
namespace MathCan.DETFACT16Saturation

def PrimeLike (p : Nat) : Prop :=
  1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem prime_divisor (n : Nat) (hn : 1 < n) :
    ∃ p, PrimeLike p ∧ p ∣ n := by
  revert hn
  refine Nat.strongRecOn n ?_
  intro m ih hm
  by_cases hd : ∃ d : Nat, d ∣ m ∧ 1 < d ∧ d < m
  · obtain ⟨d, hdm, hd1, hlt⟩ := hd
    obtain ⟨p, hp, hpd⟩ := ih d hlt hd1
    exact ⟨p, hp, Nat.dvd_trans hpd hdm⟩
  · refine ⟨m, ⟨hm, ?_⟩, Nat.dvd_refl m⟩
    intro d hdm
    have hpos := Nat.pos_of_dvd_of_pos hdm (show 0 < m by omega)
    have hle := Nat.le_of_dvd (show 0 < m by omega) hdm
    by_cases h1 : d = 1
    · exact Or.inl h1
    · by_cases h2 : d = m
      · exact Or.inr h2
      · exact False.elim (hd ⟨d, hdm, by omega, by omega⟩)

theorem strip_power (p n : Nat) (hp : 1 < p) (hn : 0 < n) :
    ∃ e r : Nat, 0 < r ∧ n = p ^ e * r ∧ ¬ p ∣ r := by
  revert hn
  refine Nat.strongRecOn n ?_
  intro m ih hm
  by_cases h : p ∣ m
  · obtain ⟨r, hr⟩ := h
    have hrpos : 0 < r := by
      by_cases hz : r = 0
      · simp [hz] at hr
        omega
      · omega
    have hlt : r < m := by
      have hh := Nat.mul_lt_mul_of_pos_right hp hrpos
      rw [Nat.one_mul] at hh
      omega
    obtain ⟨e, s, hs, heq, hnp⟩ := ih r hlt hrpos
    refine ⟨e+1, s, hs, ?_, hnp⟩
    calc
      m = p * r := hr
      _ = p * (p ^ e * s) := by rw [heq]
      _ = p ^ (e+1) * s := by
        rw [Nat.pow_succ, Nat.mul_comm (p ^ e) p, Nat.mul_assoc]
  · exact ⟨0, m, hm, by simp, h⟩

theorem prime_gcd_one_of_not_dvd (p r : Nat) (hp : PrimeLike p)
    (h : ¬ p ∣ r) : Nat.gcd p r = 1 := by
  rcases hp.2 _ (Nat.gcd_dvd_left p r) with heq | heq
  · exact heq
  · have hd := Nat.gcd_dvd_right p r
    rw [heq] at hd
    exact False.elim (h hd)

theorem distinct_prime_gcd (p q : Nat)
    (hp : PrimeLike p) (hq : PrimeLike q) (hne : p ≠ q) :
    Nat.gcd p q = 1 := by
  apply prime_gcd_one_of_not_dvd p q hp
  intro hd
  rcases hq.2 p hd with h | h
  · have := hp.1
    omega
  · exact hne h

theorem coprime_mul_dvd (x y M : Nat) (h : Nat.gcd x y = 1)
    (hx : x ∣ M) (hy : y ∣ M) : x*y ∣ M := by
  have heq : Nat.lcm x y = x*y :=
    Nat.lcm_eq_mul_iff.mpr (Or.inr (Or.inr h))
  have hd := Nat.lcm_dvd hx hy
  rwa [heq] at hd

/-- Prime-power divisibility detects arbitrary positive-integer divisibility.
This avoids assuming the fundamental theorem of arithmetic as an axiom. -/
theorem dvd_from_prime_powers (n M : Nat) (hn : 0 < n)
    (h : ∀ p e : Nat, PrimeLike p → p ^ e ∣ n → p ^ e ∣ M) :
    n ∣ M := by
  revert hn h
  refine Nat.strongRecOn n ?_
  intro m ih hm h
  by_cases hm1 : m = 1
  · simp [hm1]
  · obtain ⟨p, hp, hpd⟩ := prime_divisor m (by omega)
    obtain ⟨e, r, hr, heq, hnp⟩ := strip_power p m hp.1 hm
    have hepos : 0 < e := by
      by_cases hz : e = 0
      · have hmr : m = r := by simpa [hz] using heq
        rw [hmr] at hpd
        exact False.elim (hnp hpd)
      · omega
    have hqdiv : p ^ e ∣ m := ⟨r, heq⟩
    have hrdiv : r ∣ m := ⟨p ^ e, heq.trans (Nat.mul_comm _ _)⟩
    have hqgt : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.1
    have hlt : r < m := by
      have hh := Nat.mul_lt_mul_of_pos_right hqgt hr
      rw [Nat.one_mul] at hh
      omega
    have hrM : r ∣ M := ih r hlt hr (fun q j hq hj =>
      h q j hq (Nat.dvd_trans hj hrdiv))
    have hc : Nat.gcd (p ^ e) r = 1 :=
      Nat.gcd_pow_left_of_gcd_eq_one (prime_gcd_one_of_not_dvd p r hp hnp)
    have hd := coprime_mul_dvd (p^e) r M hc (h p e hp hqdiv) hrM
    rwa [← heq] at hd

def intervalLCM : Nat → Nat
  | 0 => 1
  | k+1 => Nat.lcm (intervalLCM k) (k+1)

theorem interval_dvd_iff (K M : Nat) :
    intervalLCM K ∣ M ↔ ∀ i : Nat, 0 < i → i ≤ K → i ∣ M := by
  induction K with
  | zero =>
    constructor
    · intro _ i hi hk
      omega
    · intro _
      exact Nat.one_dvd M
  | succ K ih =>
    change Nat.lcm (intervalLCM K) (K+1) ∣ M ↔ _
    rw [Nat.lcm_dvd_iff, ih]
    constructor
    · intro h i hi hk
      by_cases heq : i = K+1
      · simpa [heq] using h.2
      · exact h.1 i hi (by omega)
    · intro h
      exact ⟨fun i hi hk => h i hi (by omega), h (K+1) (by omega) (by omega)⟩

theorem interval_member_dvd (K i : Nat) (hi : 0 < i) (hk : i ≤ K) :
    i ∣ intervalLCM K :=
  (interval_dvd_iff K (intervalLCM K)).mp (Nat.dvd_refl _) i hi hk

abbrev Entry := Nat × Nat

def entryPower (e : Entry) : Nat := e.1 ^ e.2

def ValidEntry (K : Nat) (e : Entry) : Prop :=
  PrimeLike e.1 ∧ 0 < e.2 ∧ entryPower e ≤ K ∧ K < e.1 ^ (e.2+1)

def UniqueLabels : List Entry → Prop
  | [] => True
  | e :: es => (∀ f : Entry, f ∈ es → e.1 ≠ f.1) ∧ UniqueLabels es

def CompleteLabels (K : Nat) (es : List Entry) : Prop :=
  ∀ p : Nat, PrimeLike p → p ≤ K → ∃ e : Entry, e ∈ es ∧ e.1 = p

def rosterProduct : List Entry → Nat
  | [] => 1
  | e :: es => entryPower e * rosterProduct es

theorem entry_power_dvd_product (e : Entry) (es : List Entry)
    (h : e ∈ es) : entryPower e ∣ rosterProduct es := by
  induction es with
  | nil => simp at h
  | cons f fs ih =>
    rcases List.mem_cons.mp h with heq | hm
    · subst e
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left_of_dvd (ih hm) _

theorem gcd_roster_product (x : Nat) (es : List Entry)
    (h : ∀ e : Entry, e ∈ es → Nat.gcd x (entryPower e) = 1) :
    Nat.gcd x (rosterProduct es) = 1 := by
  induction es with
  | nil => simp [rosterProduct]
  | cons e es ih =>
    have he := h e (by simp)
    have ht : Nat.gcd x (rosterProduct es) = 1 :=
      ih (fun f hf => h f (by simp [hf]))
    change Nat.gcd x (entryPower e * rosterProduct es) = 1
    rw [Nat.gcd_mul_right_right_of_gcd_eq_one he, ht]

theorem roster_product_dvd (K M : Nat) (es : List Entry)
    (hv : ∀ e : Entry, e ∈ es → ValidEntry K e)
    (hu : UniqueLabels es) (hd : ∀ e : Entry, e ∈ es → entryPower e ∣ M) :
    rosterProduct es ∣ M := by
  induction es with
  | nil => exact Nat.one_dvd M
  | cons e es ih =>
    have he := hv e (by simp)
    have hu' : (∀ f : Entry, f ∈ es → e.1 ≠ f.1) ∧ UniqueLabels es := hu
    have ht : rosterProduct es ∣ M :=
      ih (fun f hf => hv f (by simp [hf])) hu'.2
        (fun f hf => hd f (by simp [hf]))
    have hg : Nat.gcd (entryPower e) (rosterProduct es) = 1 := by
      apply gcd_roster_product
      intro f hf
      have hcop := distinct_prime_gcd e.1 f.1 he.1
        (hv f (by simp [hf])).1 (hu'.1 f hf)
      exact Nat.pow_gcd_pow_of_gcd_eq_one hcop
    exact coprime_mul_dvd _ _ M hg (hd e (by simp)) ht

/-- Main saturation theorem. The certificate's three predicates are explicit:
valid maximal powers, no duplicate prime labels, and complete prime coverage. -/
theorem certified_roster_eq_interval_lcm (K : Nat) (es : List Entry)
    (hv : ∀ e : Entry, e ∈ es → ValidEntry K e)
    (hu : UniqueLabels es) (hc : CompleteLabels K es) :
    rosterProduct es = intervalLCM K := by
  apply Nat.dvd_antisymm
  · apply roster_product_dvd K _ es hv hu
    intro e hm
    have he := hv e hm
    apply interval_member_dvd
    · exact Nat.pow_pos (show 0 < e.1 by have := he.1.1; omega)
    · exact he.2.2.1
  · apply (interval_dvd_iff K (rosterProduct es)).mpr
    intro i hi hik
    apply dvd_from_prime_powers i _ hi
    intro p a hp hpa
    by_cases ha : a = 0
    · simp [ha]
    · have hpaK : p ^ a ≤ K :=
        Nat.le_trans (Nat.le_of_dvd hi hpa) hik
      have hpK : p ≤ K := by
        have hle : p ^ 1 ≤ p ^ a := Nat.pow_le_pow_of_le hp.1 (by omega)
        rw [Nat.pow_one] at hle
        exact Nat.le_trans hle hpaK
      obtain ⟨⟨q,b⟩, hmem, hq⟩ := hc p hp hpK
      change q = p at hq
      subst q
      have hmax : K < p ^ (b+1) := (hv (p,b) hmem).2.2.2
      have hab : a ≤ b := by
        by_cases h : a ≤ b
        · exact h
        · have hh := Nat.pow_le_pow_of_le hp.1 (show b+1 ≤ a by omega)
          omega
      exact Nat.dvd_trans (Nat.pow_dvd_pow p hab)
        (entry_power_dvd_product (p,b) es hmem)

theorem saturation_covers_group_order (H I M K : Nat)
    (hi : 0 < I) (hk : I ≤ K) (hh : H ∣ M) :
    H * I ∣ M * intervalLCM K :=
  Nat.mul_dvd_mul hh (interval_member_dvd K I hi hk)

#print axioms prime_divisor
#print axioms strip_power
#print axioms dvd_from_prime_powers
#print axioms interval_dvd_iff
#print axioms certified_roster_eq_interval_lcm
#print axioms saturation_covers_group_order
end MathCan.DETFACT16Saturation

import MathCan.DETFACT18Enumeration

/-! DETFACT-19: executable reference base list, exact first strike,
and deterministic maximal exponent lifting. Native C refinement is separate. -/
namespace MathCan.DETFACT19Construct
open MathCan.DETFACT16Saturation
open MathCan.DETFACT17OddSplit
open MathCan.DETFACT18Enumeration
open MathCan.DETFACT15Stream

def denseMark (R n : Nat) : Bool :=
  (List.range (R+1)).any (fun d => decide (1 < d ∧ d*d ≤ n ∧ d ∣ n))

theorem dense_mark_iff (R n : Nat) :
    denseMark R n = true ↔
      ∃ d, d ≤ R ∧ 1 < d ∧ d*d ≤ n ∧ d ∣ n := by
  simp [denseMark, List.any_eq_true, List.mem_range, Nat.lt_succ_iff]

theorem dense_unmarked_iff (R n : Nat) (hn : 1 < n) (hR : n ≤ R) :
    denseMark R n = false ↔ PrimeLike n := by
  constructor
  · intro hf
    by_cases hp : PrimeLike n
    · exact hp
    · obtain ⟨p,hp,hpd,hps⟩ := composite_small_prime n hn hp
      have hle := Nat.le_of_dvd (show 0 < n by omega) hpd
      have hbad := (dense_mark_iff R n).mpr ⟨p,Nat.le_trans hle hR,hp.1,hps,hpd⟩
      rw [hf] at hbad
      contradiction
  · intro hp
    cases h : denseMark R n with
    | false => rfl
    | true =>
      obtain ⟨d,_,hd1,hds,hdiv⟩ := (dense_mark_iff R n).mp h
      rcases hp.2 d hdiv with he | he
      · omega
      · have hh := Nat.mul_lt_mul_of_pos_right hd1 (show 0 < d by omega)
        rw [Nat.one_mul] at hh
        omega

theorem square_le_iff_sqrt (K p : Nat) : p*p ≤ K ↔ p ≤ Nat.sqrt K := by
  constructor
  · intro h
    by_cases hp : p ≤ Nat.sqrt K
    · exact hp
    · have hle : Nat.sqrt K+1 ≤ p := by omega
      have hs := Nat.mul_le_mul hle hle
      have ht := Nat.lt_succ_sqrt K
      change K < (Nat.sqrt K+1)*(Nat.sqrt K+1) at ht
      omega
  · intro h
    exact Nat.le_trans (Nat.mul_le_mul h h) (Nat.sqrt_le K)

def basePrimes (K : Nat) : List Nat :=
  (oddCandidates (Nat.sqrt K)).filter (fun n => !(denseMark (Nat.sqrt K) n))

theorem base_primes_iff (K p : Nat) :
    p ∈ basePrimes K ↔ PrimeLike p ∧ p ≠ 2 ∧ p*p ≤ K := by
  rw [basePrimes,List.mem_filter,mem_odd_candidates]
  constructor
  · rintro ⟨⟨hp,hR,ho⟩,hb⟩
    have hf : denseMark (Nat.sqrt K) p = false := by
      cases h : denseMark (Nat.sqrt K) p <;> simp_all
    exact ⟨(dense_unmarked_iff _ _ (by omega) hR).mp hf,by omega,
      (square_le_iff_sqrt K p).mpr hR⟩
  · rintro ⟨hp,hne,hK⟩
    have hR := (square_le_iff_sqrt K p).mp hK
    have hf := (dense_unmarked_iff _ _ hp.1 hR).mpr hp
    exact ⟨⟨by have := hp.1; omega,hR,prime_other_odd p hp hne⟩,by simp [hf]⟩

theorem base_sound (K : Nat) : BaseSound K (basePrimes K) :=
  fun p hp => (base_primes_iff K p).mp hp

theorem base_complete (K : Nat) : BaseComplete K (basePrimes K) :=
  fun p hp hn hk => (base_primes_iff K p).mpr ⟨hp,hn,hk⟩

/-- Exact ceiling quotient, including lo=0. -/
def ceilQuot (lo p : Nat) : Nat := (lo+p-1)/p

theorem ceil_quot_le_iff (lo p q : Nat) (hp : 0 < p) :
    ceilQuot lo p ≤ q ↔ lo ≤ p*q := by
  have h : (lo+p-1)/p < q+1 ↔ lo+p-1 < (q+1)*p :=
    Nat.div_lt_iff_lt_mul hp
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm q p] at h
  unfold ceilQuot
  omega

def oddUp (q : Nat) : Nat := if q%2=0 then q+1 else q

theorem odd_up_ge (q : Nat) : q ≤ oddUp q := by
  unfold oddUp
  split <;> omega

theorem odd_up_odd (q : Nat) : oddUp q % 2 = 1 := by
  unfold oddUp
  have h := Nat.mod_lt q (show 0 < 2 by decide)
  split <;> omega

theorem odd_up_le (q r : Nat) (hle : q ≤ r) (ho : r%2=1) :
    oddUp q ≤ r := by
  unfold oddUp
  split <;> omega

def strikeQuot (p lo : Nat) : Nat := oddUp (max p (ceilQuot lo p))
def firstStrike (p lo : Nat) : Nat := p*strikeQuot p lo

def firstNative (p lo : Nat) : Nat :=
  let f := max (p*p) (ceilQuot lo p * p)
  if f%2=0 then f+p else f

theorem odd_mul_parity (p q : Nat) (hp : p%2=1) :
    (p*q)%2=q%2 := by
  calc
    (p*q)%2 = ((p%2)*q)%2 := (reduce_left p q 2).symm
    _ = q%2 := by rw [hp,Nat.one_mul]

theorem native_first_eq (p lo : Nat) (ho : p%2=1) :
    firstNative p lo = firstStrike p lo := by
  have hmax : max (p*p) (ceilQuot lo p * p) = p*max p (ceilQuot lo p) := by
    by_cases h : p ≤ ceilQuot lo p
    · rw [Nat.max_eq_right (Nat.mul_le_mul_right p h),Nat.max_eq_right h,
        Nat.mul_comm (ceilQuot lo p) p]
    · have h' : ceilQuot lo p ≤ p := by omega
      rw [Nat.max_eq_left (Nat.mul_le_mul_right p h'),Nat.max_eq_left h']
  unfold firstNative firstStrike strikeQuot oddUp
  simp only [hmax,odd_mul_parity p _ ho]
  split <;> simp [Nat.mul_add]

theorem first_bounds (p lo : Nat) (hp : 0 < p) :
    p*p ≤ firstStrike p lo ∧ lo ≤ firstStrike p lo := by
  have h₁ : p ≤ strikeQuot p lo :=
    Nat.le_trans (Nat.le_max_left _ _) (odd_up_ge _)
  have h₂ : ceilQuot lo p ≤ strikeQuot p lo :=
    Nat.le_trans (Nat.le_max_right _ _) (odd_up_ge _)
  exact ⟨Nat.mul_le_mul_left p h₁,(ceil_quot_le_iff lo p _ hp).mp h₂⟩

theorem first_odd (p lo : Nat) (ho : p%2=1) :
    firstStrike p lo % 2 = 1 := by
  unfold firstStrike
  rw [odd_mul_parity _ _ ho]
  exact odd_up_odd _

/-- Characterize all eligible odd multiples in the segment's half-line. -/
theorem strike_progression_iff (p lo n : Nat) (hp : 0 < p)
    (hpo : p%2=1) (hlo : lo ≤ n) (hno : n%2=1) :
    (p*p ≤ n ∧ p ∣ n) ↔ ∃ t, n = firstStrike p lo + 2*(p*t) := by
  constructor
  · rintro ⟨hs,hd⟩
    obtain ⟨q,heq⟩ := hd
    have hq : p ≤ q := Nat.le_of_mul_le_mul_left (by omega : p*p ≤ p*q) hp
    have hqo : q%2=1 := by
      rw [heq,odd_mul_parity _ _ hpo] at hno
      exact hno
    have hceil : ceilQuot lo p ≤ q :=
      (ceil_quot_le_iff lo p q hp).mpr (by omega)
    have hge : strikeQuot p lo ≤ q :=
      odd_up_le _ _ (Nat.max_le.mpr ⟨hq,hceil⟩) hqo
    have hodd : strikeQuot p lo % 2 = 1 := odd_up_odd _
    have hdecomp : q = strikeQuot p lo + 2*((q-strikeQuot p lo)/2) := by omega
    refine ⟨(q-strikeQuot p lo)/2,?_⟩
    calc
      n = p*q := heq
      _ = p*(strikeQuot p lo + 2*((q-strikeQuot p lo)/2)) :=
        congrArg (fun x => p*x) hdecomp
      _ = firstStrike p lo + 2*(p*((q-strikeQuot p lo)/2)) := by
        unfold firstStrike
        rw [Nat.mul_add]
        ac_rfl
  · rintro ⟨t,heq⟩
    refine ⟨?_,?_⟩
    · have hh := (first_bounds p lo hp).1
      omega
    · refine ⟨strikeQuot p lo+2*t,?_⟩
      rw [heq,firstStrike,Nat.mul_add]
      ac_rfl

def firstOffset (p lo : Nat) : Nat := (firstNative p lo-lo)/2

/-- The native slot progression starts exactly at firstOffset and steps by p. -/
theorem native_offset_iff (p lo h : Nat) (hp : 0 < p)
    (hpo : p%2=1) (hlo : lo%2=1) :
    (p*p ≤ lo+2*h ∧ p ∣ lo+2*h) ↔
      ∃ t, h = firstOffset p lo + p*t := by
  have hb := (first_bounds p lo hp).2
  have ho := first_odd p lo hpo
  have hdec : firstStrike p lo = lo+2*((firstStrike p lo-lo)/2) := by omega
  have hn : (lo+2*h)%2=1 := by omega
  rw [strike_progression_iff p lo (lo+2*h) hp hpo (by omega) hn]
  unfold firstOffset
  rw [native_first_eq p lo hpo]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t,by omega⟩
  · rintro ⟨t,ht⟩
    exact ⟨t,by omega⟩

/-- Division recurrence; the fuel K is a mathematical termination bound.
On p>1 only logarithmically many recursive calls are used. -/
def maxExpFuel (p : Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | fuel+1,k => if p ≤ k then maxExpFuel p fuel (k/p)+1 else 0

def maxExp (p K : Nat) : Nat := maxExpFuel p K K

theorem max_exp_fuel_correct (p fuel k : Nat) (hp : 1 < p)
    (hk : 1 ≤ k) (hf : k ≤ fuel) :
    p^(maxExpFuel p fuel k) ≤ k ∧ k < p^(maxExpFuel p fuel k+1) := by
  induction fuel generalizing k with
  | zero => omega
  | succ f ih =>
    by_cases h : p ≤ k
    · have hp0 : 0 < p := by omega
      have hpos : 1 ≤ k/p := (Nat.le_div_iff_mul_le hp0).mpr (by simpa using h)
      have hlt := Nat.div_lt_self (show 0 < k by omega) hp
      obtain ⟨hl,hu⟩ := ih (k/p) hpos (by omega)
      simp only [maxExpFuel,if_pos h]
      constructor
      · rw [Nat.pow_succ]
        exact (Nat.le_div_iff_mul_le hp0).mp hl
      · rw [Nat.pow_succ p (maxExpFuel p f (k/p)+1)]
        exact (Nat.div_lt_iff_lt_mul hp0).mp hu
    · simp only [maxExpFuel,if_neg h,Nat.pow_zero,Nat.zero_add,Nat.pow_one]
      exact ⟨hk,by omega⟩

theorem max_exp_correct (p K : Nat) (hp : 1 < p) (hk : 1 ≤ K) :
    p^maxExp p K ≤ K ∧ K < p^(maxExp p K+1) :=
  max_exp_fuel_correct p K K hp hk (Nat.le_refl K)

def makeEntry (K p : Nat) : Entry := (p,maxExp p K)

def roster (K : Nat) : List Entry :=
  (enumeratedLabels K (basePrimes K)).map (makeEntry K)

theorem map_entry_unique (K : Nat) (ps : List Nat) (hu : ps.Nodup) :
    UniqueLabels (ps.map (makeEntry K)) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    have hn := List.nodup_cons.mp hu
    change (∀ f : Entry, f ∈ ps.map (makeEntry K) → p ≠ f.1) ∧
      UniqueLabels (ps.map (makeEntry K))
    refine ⟨?_,ih hn.2⟩
    intro f hf he
    obtain ⟨q,hq,hf'⟩ := List.mem_map.mp hf
    rw [← hf'] at he
    change p = q at he
    rw [← he] at hq
    exact hn.1 hq

theorem roster_valid (K : Nat) (e : Entry) (hm : e ∈ roster K) :
    ValidEntry K e := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have hp' := (labels_iff K p (basePrimes K) (base_sound K) (base_complete K)).mp hp
  have hh := max_exp_correct p K hp'.1.1 (by have := hp'.1.1; omega)
  have hpos : 0 < maxExp p K := by
    by_cases h : maxExp p K = 0
    · have hu := hh.2
      simp [h] at hu
      omega
    · omega
  exact ⟨hp'.1,hpos,hh.1,hh.2⟩

theorem roster_unique (K : Nat) : UniqueLabels (roster K) :=
  map_entry_unique K _ (labels_nodup K (basePrimes K))

theorem roster_complete (K : Nat) : CompleteLabels K (roster K) := by
  intro p hp hk
  have hm := (labels_iff K p (basePrimes K) (base_sound K) (base_complete K)).mpr ⟨hp,hk⟩
  exact ⟨makeEntry K p,List.mem_map_of_mem hm,rfl⟩

theorem constructed_roster_lcm (K : Nat) :
    rosterProduct (roster K) = intervalLCM K :=
  certified_roster_eq_interval_lcm K (roster K) (roster_valid K)
    (roster_unique K) (roster_complete K)

theorem constructed_split_probe (K M s u n a j : Nat)
    (hM : M = 2^s*u) (ho : Odd u) :
    splitProbe n (execute n a (oddStream u (roster K))) j =
      Nat.gcd (gcdInput
        (a^(((2*M*intervalLCM K)/2^(splitCount s (roster K)))*2^j)%n)) n :=
  saturated_stream_split_probe K M s u n a j (roster K) hM ho
    (roster_valid K) (roster_unique K) (roster_complete K)

#print axioms base_primes_iff
#print axioms native_first_eq
#print axioms native_offset_iff
#print axioms max_exp_correct
#print axioms constructed_roster_lcm
#print axioms constructed_split_probe
end MathCan.DETFACT19Construct

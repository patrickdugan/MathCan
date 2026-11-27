import MathCan.DETFACT17OddSplit

/-!
DETFACT-18: abstract segmented enumeration and certificate construction.
The native byte-array marking loops and C source refinement are separate.
-/
namespace MathCan.DETFACT18Enumeration
open MathCan.DETFACT16Saturation
open MathCan.DETFACT17OddSplit

theorem no_proper_divisor_prime (n : Nat) (hn : 1 < n)
    (h : ¬ ∃ d : Nat, d ∣ n ∧ 1 < d ∧ d < n) : PrimeLike n := by
  refine ⟨hn, ?_⟩
  intro d hd
  have hp := Nat.pos_of_dvd_of_pos hd (show 0 < n by omega)
  have hl := Nat.le_of_dvd (show 0 < n by omega) hd
  by_cases h1 : d = 1
  · exact Or.inl h1
  · by_cases hn' : d = n
    · exact Or.inr hn'
    · exact False.elim (h ⟨d,hd,by omega,by omega⟩)

theorem composite_small_prime (n : Nat) (hn : 1 < n)
    (h : ¬ PrimeLike n) :
    ∃ p : Nat, PrimeLike p ∧ p ∣ n ∧ p*p ≤ n := by
  by_cases hd : ∃ d : Nat, d ∣ n ∧ 1 < d ∧ d < n
  · obtain ⟨d,hdiv,hd1,hdn⟩ := hd
    obtain ⟨q,heq⟩ := hdiv
    have hq1 : 1 < q := by
      by_cases hz : q = 0
      · simp [hz] at heq
        omega
      · by_cases ho : q = 1
        · simp [ho] at heq
          omega
        · omega
    by_cases hle : d ≤ q
    · obtain ⟨p,hp,hpd⟩ := prime_divisor d hd1
      have hpl := Nat.le_of_dvd (show 0 < d by omega) hpd
      have hsq : p*p ≤ d*q :=
        Nat.mul_le_mul hpl (Nat.le_trans hpl hle)
      exact ⟨p,hp,Nat.dvd_trans hpd ⟨q,heq⟩,by omega⟩
    · obtain ⟨p,hp,hpq⟩ := prime_divisor q hq1
      have hpl := Nat.le_of_dvd (show 0 < q by omega) hpq
      have hqd : q ∣ n := ⟨d,heq.trans (Nat.mul_comm _ _)⟩
      have hsq : p*p ≤ d*q :=
        Nat.mul_le_mul (Nat.le_trans hpl (by omega)) hpl
      exact ⟨p,hp,Nat.dvd_trans hpq hqd,by omega⟩
  · exact False.elim (h (no_proper_divisor_prime n hn hd))

theorem prime_not_struck (n p : Nat) (hn : PrimeLike n)
    (hp : PrimeLike p) (hd : p ∣ n) (hs : p*p ≤ n) : False := by
  rcases hn.2 p hd with h | h
  · have := hp.1
    omega
  · have hh := Nat.mul_lt_mul_of_pos_right hp.1 (show 0 < p by have := hp.1; omega)
    rw [Nat.one_mul] at hh
    omega

/-- The native odd marking progression starts at p² and increments by 2p. -/
theorem odd_strike_progression (p n : Nat) (hp : PrimeLike p)
    (hp2 : p ≠ 2) (hn : n % 2 = 1) (hs : p*p ≤ n) (hd : p ∣ n) :
    ∃ t : Nat, n = p*(p+2*t) := by
  obtain ⟨q,heq⟩ := hd
  have hpodd : p % 2 = 1 := prime_other_odd p hp hp2
  have hpos : 0 < p := by have := hp.1; omega
  have hqge : p ≤ q :=
    Nat.le_of_mul_le_mul_left (by omega : p*p ≤ p*q) hpos
  have hqodd : q % 2 = 1 := by
    have hlt := Nat.mod_lt q (show 0 < 2 by decide)
    by_cases hz : q % 2 = 0
    · have hqd : 2 ∣ q := Nat.dvd_of_mod_eq_zero hz
      have hqn : q ∣ n := ⟨p,heq.trans (Nat.mul_comm _ _)⟩
      have hbad := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hqd hqn)
      omega
    · omega
  have hq : q = p+2*((q-p)/2) := by omega
  exact ⟨(q-p)/2,heq.trans (congrArg (fun x => p*x) hq)⟩

def BaseSound (K : Nat) (ps : List Nat) : Prop :=
  ∀ p, p ∈ ps → PrimeLike p ∧ p ≠ 2 ∧ p*p ≤ K

def BaseComplete (K : Nat) (ps : List Nat) : Prop :=
  ∀ p, PrimeLike p → p ≠ 2 → p*p ≤ K → p ∈ ps

def baseMark (ps : List Nat) (n : Nat) : Bool :=
  ps.any (fun p => decide (p*p ≤ n ∧ p ∣ n))

theorem base_mark_iff (ps : List Nat) (n : Nat) :
    baseMark ps n = true ↔ ∃ p, p ∈ ps ∧ p*p ≤ n ∧ p ∣ n := by
  simp [baseMark, List.any_eq_true]

theorem unmarked_iff_prime (K n : Nat) (ps : List Nat)
    (hs : BaseSound K ps) (hc : BaseComplete K ps)
    (hn : 3 ≤ n) (hk : n ≤ K) (ho : n % 2 = 1) :
    baseMark ps n = false ↔ PrimeLike n := by
  constructor
  · intro h
    by_cases hp : PrimeLike n
    · exact hp
    · obtain ⟨p,hp,hpd,hps⟩ := composite_small_prime n (by omega) hp
      have hne : p ≠ 2 := by
        intro he
        rw [he] at hpd
        have hz := Nat.mod_eq_zero_of_dvd hpd
        omega
      have hm := hc p hp hne (Nat.le_trans hps hk)
      have hb := (base_mark_iff ps n).mpr ⟨p,hm,hps,hpd⟩
      rw [h] at hb
      contradiction
  · intro hp
    cases h : baseMark ps n with
    | false => rfl
    | true =>
      obtain ⟨p,hm,hps,hpd⟩ := (base_mark_iff ps n).mp h
      exact False.elim (prime_not_struck n p hp (hs p hm).1 hpd hps)

def oddCandidates (K : Nat) : List Nat :=
  List.range' 3 ((K-1)/2) 2

theorem mem_odd_candidates (K n : Nat) :
    n ∈ oddCandidates K ↔ 3 ≤ n ∧ n ≤ K ∧ n % 2 = 1 := by
  rw [oddCandidates,List.mem_range']
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨hn,hk,ho⟩
    exact ⟨(n-3)/2,by omega,by omega⟩

def segmentCandidates (K S j : Nat) : List Nat :=
  List.range' (3+2*(j*S)) (min S ((K-1)/2-j*S)) 2

theorem mem_segment (K S j n : Nat) :
    n ∈ segmentCandidates K S j ↔
      ∃ h, h < S ∧ j*S+h < (K-1)/2 ∧ n = 3+2*(j*S+h) := by
  rw [segmentCandidates,List.mem_range']
  constructor
  · rintro ⟨h,hh,he⟩
    have hm := Nat.lt_min.mp hh
    exact ⟨h,hm.1,by omega,by omega⟩
  · rintro ⟨h,hh,hcount,he⟩
    exact ⟨h,Nat.lt_min.mpr ⟨hh,by omega⟩,by omega⟩

theorem segment_member_global (K S j n : Nat)
    (h : n ∈ segmentCandidates K S j) : n ∈ oddCandidates K := by
  obtain ⟨i,_,hi,he⟩ := (mem_segment K S j n).mp h
  rw [oddCandidates,List.mem_range']
  exact ⟨j*S+i,hi,he⟩

/-- Every eligible odd integer lies in exactly one truncated segment. -/
theorem unique_segment (K S n : Nat) (hS : 0 < S)
    (hn : n ∈ oddCandidates K) :
    ∃ j, n ∈ segmentCandidates K S j ∧
      ∀ j', n ∈ segmentCandidates K S j' → j' = j := by
  have hn' : n ∈ List.range' 3 ((K-1)/2) 2 := hn
  obtain ⟨i,hi,he⟩ := List.mem_range'.mp hn'
  have hdec : (i/S)*S+i%S=i := by
    rw [Nat.mul_comm (i/S) S]
    exact Nat.div_add_mod i S
  refine ⟨i/S,(mem_segment K S (i/S) n).mpr
    ⟨i%S,Nat.mod_lt _ hS,by omega,by omega⟩,?_⟩
  intro j' hj'
  obtain ⟨h,hlt,hbound,he'⟩ := (mem_segment K S j' n).mp hj'
  have hlo : j'*S ≤ i := by omega
  have hhi : i < (j'+1)*S := by rw [Nat.add_mul,Nat.one_mul]; omega
  exact (Nat.div_eq_of_lt_le hlo hhi).symm

def oddSurvivors (K : Nat) (ps : List Nat) : List Nat :=
  (oddCandidates K).filter (fun n => !(baseMark ps n))

theorem odd_survivor_iff (K n : Nat) (ps : List Nat)
    (hs : BaseSound K ps) (hc : BaseComplete K ps) :
    n ∈ oddSurvivors K ps ↔ 3 ≤ n ∧ n ≤ K ∧ n % 2 = 1 ∧ PrimeLike n := by
  rw [oddSurvivors,List.mem_filter,mem_odd_candidates]
  constructor
  · rintro ⟨⟨hn,hk,ho⟩,hb⟩
    have hf : baseMark ps n = false := by
      cases h : baseMark ps n <;> simp_all
    exact ⟨hn,hk,ho,(unmarked_iff_prime K n ps hs hc hn hk ho).mp hf⟩
  · rintro ⟨hn,hk,ho,hp⟩
    have hf := (unmarked_iff_prime K n ps hs hc hn hk ho).mpr hp
    exact ⟨⟨hn,hk,ho⟩,by simp [hf]⟩

def enumeratedLabels (K : Nat) (ps : List Nat) : List Nat :=
  if 2 ≤ K then 2 :: oddSurvivors K ps else oddSurvivors K ps

theorem labels_iff (K p : Nat) (ps : List Nat)
    (hs : BaseSound K ps) (hc : BaseComplete K ps) :
    p ∈ enumeratedLabels K ps ↔ PrimeLike p ∧ p ≤ K := by
  by_cases h : 2 ≤ K
  · rw [enumeratedLabels,if_pos h,List.mem_cons,odd_survivor_iff K p ps hs hc]
    constructor
    · rintro (rfl | ⟨_,hk,_,hp⟩)
      · exact ⟨prime_two,h⟩
      · exact ⟨hp,hk⟩
    · rintro ⟨hp,hk⟩
      by_cases he : p = 2
      · exact Or.inl he
      · exact Or.inr ⟨by have := hp.1; omega,hk,prime_other_odd p hp he,hp⟩
  · rw [enumeratedLabels,if_neg h,odd_survivor_iff K p ps hs hc]
    constructor
    · rintro ⟨hn,hk,_,_⟩
      omega
    · rintro ⟨hp,hk⟩
      have := hp.1
      omega

theorem labels_nodup (K : Nat) (ps : List Nat) :
    (enumeratedLabels K ps).Nodup := by
  have hn : (oddCandidates K).Nodup := List.nodup_range' 2
  have hf : (oddSurvivors K ps).Nodup := List.Sublist.nodup List.filter_sublist hn
  by_cases h : 2 ≤ K
  · rw [enumeratedLabels,if_pos h,List.nodup_cons]
    refine ⟨?_,hf⟩
    intro hm
    have hm' := (List.mem_filter.mp hm).1
    have hh := (mem_odd_candidates K 2).mp hm'
    omega
  · simpa only [enumeratedLabels,if_neg h] using hf

theorem maximal_exists (p K : Nat) (hp : 1 < p) (hK : 1 ≤ K) :
    ∃ e : Nat, p^e ≤ K ∧ K < p^(e+1) := by
  revert hK
  induction K with
  | zero => omega
  | succ K ih =>
    intro hK
    by_cases hz : K = 0
    · exact ⟨0,by simp [hz],by simpa [hz] using hp⟩
    · obtain ⟨e,hl,hu⟩ := ih (by omega)
      by_cases h : K+1 < p^(e+1)
      · exact ⟨e,by omega,h⟩
      · have hh : p^(e+1) < p^(e+1+1) := Nat.pow_lt_pow_succ hp
        exact ⟨e+1,by omega,by omega⟩

/-- Lifting a unique list of eligible primes to valid maximal powers.
This is an existence theorem, not an implementation of the exponent search. -/
theorem lift_labels (K : Nat) (ps : List Nat)
    (hv : ∀ p, p ∈ ps → PrimeLike p ∧ p ≤ K) (hu : ps.Nodup) :
    ∃ es : List Entry, es.map Prod.fst = ps ∧
      (∀ e : Entry, e ∈ es → ValidEntry K e) ∧ UniqueLabels es := by
  induction ps with
  | nil => exact ⟨[],rfl,by simp,True.intro⟩
  | cons p ps ih =>
    have hp := hv p (by simp)
    have hn := List.nodup_cons.mp hu
    obtain ⟨es,hm,hvalid,hunique⟩ := ih (fun q hq => hv q (by simp [hq])) hn.2
    obtain ⟨e,hl,hh⟩ := maximal_exists p K hp.1.1 (by have := hp.1.1; omega)
    have he : 0 < e := by
      by_cases hz : e = 0
      · simp [hz] at hh
        omega
      · omega
    refine ⟨(p,e)::es,by simp [hm],?_,?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | ht
      · exact ⟨hp.1,he,hl,hh⟩
      · exact hvalid f ht
    · refine ⟨?_,hunique⟩
      intro f hf heq
      have hmem : f.1 ∈ ps := by
        rw [← hm]
        exact List.mem_map_of_mem hf
      rw [← heq] at hmem
      exact hn.1 hmem

theorem enumerated_roster_lcm (K : Nat) (ps : List Nat)
    (hs : BaseSound K ps) (hc : BaseComplete K ps) :
    ∃ es : List Entry, es.map Prod.fst = enumeratedLabels K ps ∧
      (∀ e : Entry, e ∈ es → ValidEntry K e) ∧ UniqueLabels es ∧
      CompleteLabels K es ∧ rosterProduct es = intervalLCM K := by
  obtain ⟨es,hm,hv,hu⟩ := lift_labels K (enumeratedLabels K ps)
    (fun p hp => (labels_iff K p ps hs hc).mp hp) (labels_nodup K ps)
  have hcomplete : CompleteLabels K es := by
    intro p hp hk
    have hmem := (labels_iff K p ps hs hc).mpr ⟨hp,hk⟩
    rw [← hm] at hmem
    exact List.mem_map.mp hmem
  exact ⟨es,hm,hv,hu,hcomplete,certified_roster_eq_interval_lcm K es hv hu hcomplete⟩

#print axioms composite_small_prime
#print axioms odd_strike_progression
#print axioms unmarked_iff_prime
#print axioms unique_segment
#print axioms labels_iff
#print axioms labels_nodup
#print axioms enumerated_roster_lcm
end MathCan.DETFACT18Enumeration

import MathCan.ZKLean

/-! ZKL-29: independent specifications and theorems for the settlement circuits.

Scope. This file states, over `Nat`/`Int`/`List`, the properties P1, P2, P3/P4, P6, P7, P8
and P9 of `research/zk_lean/ZKL29_SETTLEMENT_AUDIT.md`. It reads no Rust, no R1CS and no
Nova artifact. Every theorem is followed by `#print axioms`.

What is proven: the arithmetic of the clearing waterfall (exact pro-rata with the remainder
rule of `clearing.rs:187-194`, priority order, ledger identity per batch and along a bound
trace), injectivity of fixed-width encodings, binding of digests, chains, state commitments
and Merkle paths under an explicit collision-resistance hypothesis, nullifier non-replay,
canonical integer encoding with field-wrap exclusion (and the counterexample without the
bound), and the exact fold count.

What is not proven: that any R1CS gadget refines these specifications, that the relaxed
R1CS of Nova folding refines the ordinary R1CS, SHA-256 collision resistance, Nova
knowledge soundness, Rust refinement. Collision resistance occurs only as a hypothesis of
the theorems that need it; it is never an axiom. -/
namespace MathCan.ZKLean.Settlement

open MathCan.ZKLean

/-! ## Sums -/

def sumL : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumL xs

theorem sumL_append (a b : List Nat) : sumL (a ++ b) = sumL a + sumL b := by
  induction a with
  | nil => simp [sumL]
  | cons x xs ih => simp [sumL, ih, Nat.add_assoc]
#print axioms sumL_append

/-! ## P2: exact pro-rata (`clearing.rs:187-194`, `gadgets.rs:220-260`) -/

/-- Pairs `(amount, floor share)`, floor share `total * a / sum` (`clearing.rs:190`). -/
def floors (total : Nat) (amounts : List Nat) : List (Nat × Nat) :=
  amounts.map (fun a => (a, total * a / sumL amounts))

/-- Remainder rule of `clearing.rs:192`: `x = rest.min(a - o); o += x; rest -= x`, in order. -/
def dist : Nat → List (Nat × Nat) → List Nat
  | _, [] => []
  | rest, (a, o) :: ps => (o + min rest (a - o)) :: dist (rest - min rest (a - o)) ps

/-- `clearing::prorata`: zeros when the sum or the total is zero, else floors then remainder. -/
def prorata (total : Nat) (amounts : List Nat) : List Nat :=
  if sumL amounts = 0 ∨ total = 0 then amounts.map (fun _ => 0)
  else dist (total - sumL ((floors total amounts).map Prod.snd)) (floors total amounts)

/-- Every share lies between its floor and its amount. -/
def Caps : List (Nat × Nat) → List Nat → Prop
  | [], [] => True
  | (a, o) :: ps, s :: ss => o ≤ s ∧ s ≤ a ∧ Caps ps ss
  | _, _ => False

/-- Remainder priority: a prefix of items is filled to its amount, then at most one item is
partially filled, and every later item keeps its floor. -/
def Prio : List (Nat × Nat) → List Nat → Prop
  | [], [] => True
  | (a, o) :: ps, s :: ss =>
      (s = a ∧ Prio ps ss) ∨ (s ≤ a ∧ o ≤ s ∧ ss = ps.map Prod.snd)
  | _, _ => False

theorem dist_zero (ps : List (Nat × Nat)) : dist 0 ps = ps.map Prod.snd := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨a, o⟩ := p
    simp [dist, ih]
#print axioms dist_zero

theorem dist_sum (ps : List (Nat × Nat)) (hle : ∀ p ∈ ps, p.2 ≤ p.1) :
    ∀ rest, rest ≤ sumL (ps.map fun p => p.1 - p.2) →
      sumL (dist rest ps) = sumL (ps.map Prod.snd) + rest := by
  induction ps with
  | nil => intro rest h; simp [sumL] at h; simp [dist, sumL, h]
  | cons p ps ih =>
    obtain ⟨a, o⟩ := p
    intro rest h
    have ho : o ≤ a := hle (a, o) (List.mem_cons_self ..)
    have hle' : ∀ q ∈ ps, q.2 ≤ q.1 := fun q hq => hle q (List.mem_cons_of_mem _ hq)
    simp only [List.map, sumL] at h
    have h1 : rest - min rest (a - o) ≤ sumL (ps.map fun p => p.1 - p.2) := by omega
    have := ih hle' (rest - min rest (a - o)) h1
    simp only [dist, sumL, List.map]
    omega
#print axioms dist_sum

theorem dist_caps (ps : List (Nat × Nat)) (hle : ∀ p ∈ ps, p.2 ≤ p.1) :
    ∀ rest, Caps ps (dist rest ps) := by
  induction ps with
  | nil => intro rest; exact True.intro
  | cons p ps ih =>
    obtain ⟨a, o⟩ := p
    intro rest
    have ho : o ≤ a := hle (a, o) (List.mem_cons_self ..)
    have hle' : ∀ q ∈ ps, q.2 ≤ q.1 := fun q hq => hle q (List.mem_cons_of_mem _ hq)
    simp only [dist, Caps]
    exact ⟨by omega, by omega, ih hle' _⟩
#print axioms dist_caps

theorem dist_prio (ps : List (Nat × Nat)) (hle : ∀ p ∈ ps, p.2 ≤ p.1) :
    ∀ rest, Prio ps (dist rest ps) := by
  induction ps with
  | nil => intro rest; exact True.intro
  | cons p ps ih =>
    obtain ⟨a, o⟩ := p
    intro rest
    have ho : o ≤ a := hle (a, o) (List.mem_cons_self ..)
    have hle' : ∀ q ∈ ps, q.2 ≤ q.1 := fun q hq => hle q (List.mem_cons_of_mem _ hq)
    simp only [dist, Prio]
    by_cases h : a - o ≤ rest
    · exact Or.inl ⟨by omega, ih hle' _⟩
    · have hr : rest - min rest (a - o) = 0 := by omega
      refine Or.inr ⟨by omega, by omega, ?_⟩
      rw [hr, dist_zero]
#print axioms dist_prio

/-- Pairing lemma: amounts minus floors plus floors is the sum of the amounts. -/
theorem sum_gap (ps : List (Nat × Nat)) (hle : ∀ p ∈ ps, p.2 ≤ p.1) :
    sumL (ps.map fun p => p.1 - p.2) + sumL (ps.map Prod.snd) = sumL (ps.map Prod.fst) := by
  induction ps with
  | nil => simp [sumL]
  | cons p ps ih =>
    obtain ⟨a, o⟩ := p
    have ho : o ≤ a := hle (a, o) (List.mem_cons_self ..)
    have hle' : ∀ q ∈ ps, q.2 ≤ q.1 := fun q hq => hle q (List.mem_cons_of_mem _ hq)
    have := ih hle'
    simp only [List.map, sumL]
    omega
#print axioms sum_gap

theorem floors_fst (total : Nat) (amounts : List Nat) :
    (floors total amounts).map Prod.fst = amounts := by
  simp [floors, List.map_map, Function.comp_def]
#print axioms floors_fst

theorem floors_le (total : Nat) (amounts : List Nat) (h : total ≤ sumL amounts) :
    ∀ p ∈ floors total amounts, p.2 ≤ p.1 := by
  intro p hp
  simp only [floors, List.mem_map] at hp
  obtain ⟨a, _, rfl⟩ := hp
  apply Nat.div_le_of_le_mul
  exact Nat.mul_le_mul_right a h
#print axioms floors_le

/-- Sum of floors times the denominator never exceeds `total * sum`. -/
theorem floors_sum_mul (total S : Nat) (amounts : List Nat) :
    sumL (amounts.map fun a => total * a / S) * S ≤ total * sumL amounts := by
  induction amounts with
  | nil => simp [sumL]
  | cons a as ih =>
    simp only [List.map, sumL]
    have h1 : total * a / S * S ≤ total * a := Nat.div_mul_le_self (total * a) S
    rw [Nat.add_mul, Nat.mul_add]
    omega
#print axioms floors_sum_mul

theorem floors_sum_le (total : Nat) (amounts : List Nat) (hS : 0 < sumL amounts) : sumL ((floors total amounts).map Prod.snd) ≤ total := by
  have h1 := floors_sum_mul total (sumL amounts) amounts
  have h2 : (floors total amounts).map Prod.snd = amounts.map fun a => total * a / sumL amounts := by
    simp [floors, List.map_map, Function.comp_def]
  rw [h2]
  exact Nat.le_of_mul_le_mul_right h1 hS
#print axioms floors_sum_le

/-- Exactness: shares sum to the total (floors plus remainder, nothing lost or created). -/
theorem prorata_sum (total : Nat) (amounts : List Nat) (h : total ≤ sumL amounts) :
    sumL (prorata total amounts) = total := by
  unfold prorata
  by_cases hz : sumL amounts = 0 ∨ total = 0
  · rw [if_pos hz]
    have : total = 0 := by omega
    subst this
    clear hz h
    induction amounts with
    | nil => simp [sumL]
    | cons a as ih => simp [sumL, ih]
  · rw [if_neg hz]
    have hS : 0 < sumL amounts := by omega
    have hle := floors_le total amounts h
    have hfl := floors_sum_le total amounts hS
    have hgap := sum_gap (floors total amounts) hle
    rw [floors_fst] at hgap
    have := dist_sum (floors total amounts) hle
      (total - sumL ((floors total amounts).map Prod.snd)) (by omega)
    omega
#print axioms prorata_sum

/-- Every share is at most its amount and at least its floor. -/
theorem prorata_caps (total : Nat) (amounts : List Nat) (h : total ≤ sumL amounts)
    (hz : ¬ (sumL amounts = 0 ∨ total = 0)) :
    Caps (floors total amounts) (prorata total amounts) := by
  unfold prorata
  rw [if_neg hz]
  exact dist_caps _ (floors_le total amounts h) _
#print axioms prorata_caps

/-- Remainder priority of the clearing rule. -/
theorem prorata_priority (total : Nat) (amounts : List Nat) (h : total ≤ sumL amounts)
    (hz : ¬ (sumL amounts = 0 ∨ total = 0)) :
    Prio (floors total amounts) (prorata total amounts) := by
  unfold prorata
  rw [if_neg hz]
  exact dist_prio _ (floors_le total amounts h) _
#print axioms prorata_priority

/-! ## P2: waterfall priority (extends `allocateDefault`, `ZKLean.lean:185-199`) -/

/-- Haircuts start only when the fund is exhausted, provided carry implies an empty fund. -/
theorem allocateDefault_haircut_after_fund (shortfall fund carry base : Nat)
    (hinv : 0 < carry → fund = 0)
    (h : 0 < (allocateDefault shortfall fund carry base).haircut) :
    (allocateDefault shortfall fund carry base).fundUsed = fund := by
  change 0 < min (shortfall - min shortfall fund + carry) base at h
  change min shortfall fund = fund
  rcases Nat.eq_zero_or_pos carry with hc | hc
  · omega
  · have := hinv hc
    omega
#print axioms allocateDefault_haircut_after_fund

/-- Carry is created only when every claim and gain was haircut to zero. -/
theorem allocateDefault_carry_after_haircut (shortfall fund carry base : Nat)
    (h : 0 < (allocateDefault shortfall fund carry base).carry) :
    (allocateDefault shortfall fund carry base).haircut = base := by
  change 0 < shortfall - min shortfall fund + carry -
    min (shortfall - min shortfall fund + carry) base at h
  change min (shortfall - min shortfall fund + carry) base = base
  omega
#print axioms allocateDefault_carry_after_haircut

/-- The invariant "carry > 0 implies the fund is empty" survives a waterfall step. -/
theorem allocateDefault_invariant (shortfall fund carry base : Nat)
    (hinv : 0 < carry → fund = 0)
    (h : 0 < (allocateDefault shortfall fund carry base).carry) :
    fund - (allocateDefault shortfall fund carry base).fundUsed = 0 := by
  change 0 < shortfall - min shortfall fund + carry -
    min (shortfall - min shortfall fund + carry) base at h
  change fund - min shortfall fund = 0
  rcases Nat.eq_zero_or_pos carry with hc | hc
  · omega
  · have := hinv hc
    omega
#print axioms allocateDefault_invariant

/-- Loss collection order: margin first, own claim second, shortfall last. -/
theorem collectLoss_order (need released claim : Nat) :
    let l := collectLoss need released claim
    (0 < l.own → l.collected = released ∨ l.collected = need) ∧
    (0 < l.shortfall → l.own = claim ∧ l.collected = released) := by
  change (0 < min (need - min need released) claim →
      min need released = released ∨ min need released = need) ∧
    (0 < need - min need released - min (need - min need released) claim →
      min (need - min need released) claim = claim ∧ min need released = released)
  constructor
  · intro h
    rcases Nat.le_total need released with h1 | h1
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · intro h
    exact ⟨by omega, by omega⟩
#print axioms collectLoss_order

/-! ## P1: batch ledger identity from aggregated rows -/

/-- Row sums of one batch (`clearing.rs:211-268`): losses split three ways, gains, fund use,
haircut on claims and on gains, cash paid. -/
structure BatchAgg where
  collected : Nat
  own : Nat
  shortfall : Nat
  gains : Nat
  fundUsed : Nat
  cutClaims : Nat
  cutGains : Nat
  paid : Nat
  deriving Repr

structure St where
  seq : Nat
  cash : Int
  claims : Int
  fund : Int
  carry : Int
  book : Int
  deriving Repr

/-- `carry' = shortfall - fund_absorbed + carry - haircut` (`clearing.rs:231,239,252`). -/
def stepApply (s : St) (b : BatchAgg) : St where
  seq := s.seq + 1
  cash := s.cash + b.collected - b.paid
  claims := s.claims - b.own - b.cutClaims + b.gains - b.cutGains - b.paid
  fund := s.fund - b.fundUsed
  carry := b.shortfall - b.fundUsed + s.carry - b.cutClaims - b.cutGains
  book := s.book + b.collected + b.own + b.shortfall - b.gains

def Valid (s : St) (b : BatchAgg) : Prop :=
  b.fundUsed ≤ b.shortfall ∧ b.fundUsed ≤ s.fund ∧
  (b.cutClaims + b.cutGains : Int) ≤ b.shortfall - b.fundUsed + s.carry

def ClearStep (s t : St) : Prop := ∃ b, Valid s b ∧ t = stepApply s b

theorem batch_delta (s : St) (b : BatchAgg) :
    let t := stepApply s b
    (t.cash - s.cash) - (t.claims - s.claims) - (t.fund - s.fund) + (t.carry - s.carry)
      = t.book - s.book := by
  simp only [stepApply]
  omega
#print axioms batch_delta

theorem batch_preserves_identity (s : St) (b : BatchAgg)
    (h : ledgerIdentity s.cash s.claims s.fund s.carry s.book) :
    ledgerIdentity (stepApply s b).cash (stepApply s b).claims (stepApply s b).fund
      (stepApply s b).carry (stepApply s b).book := by
  unfold ledgerIdentity at *
  simp only [stepApply]
  omega
#print axioms batch_preserves_identity

theorem clearStep_identity {s t : St} (h : ClearStep s t)
    (hs : ledgerIdentity s.cash s.claims s.fund s.carry s.book) :
    ledgerIdentity t.cash t.claims t.fund t.carry t.book := by
  obtain ⟨b, _, rfl⟩ := h
  exact batch_preserves_identity s b hs
#print axioms clearStep_identity

/-- Net settlement vector sums to zero with the pool line (`clearing.rs:272`). -/
theorem batch_net_zero (s : St) (b : BatchAgg) :
    ((b.paid : Int) - b.collected) + ((stepApply s b).cash - s.cash) = 0 := by
  simp only [stepApply]
  omega
#print axioms batch_net_zero

/-- Cash never falls below `min cash 0` (`clearing.rs:273`). -/
theorem batch_cash_floor (s : St) (b : BatchAgg)
    (h : (b.paid : Int) ≤ max (s.cash + b.collected) 0) :
    min s.cash 0 ≤ (stepApply s b).cash := by
  simp only [stepApply]
  omega
#print axioms batch_cash_floor

/-! ## P9: exact fold count, initial and terminal state -/

theorem step_seq {s t : St} (h : ClearStep s t) : t.seq = s.seq + 1 := by
  obtain ⟨b, _, rfl⟩ := h
  rfl
#print axioms step_seq

theorem trace_seq {n : Nat} {s t : St} (h : Trace ClearStep n s t) : t.seq = s.seq + n := by
  induction h with
  | nil => rfl
  | snoc _ hs ih => rw [step_seq hs, ih]; rfl
#print axioms trace_seq

/-- The pinned initial and terminal sequence numbers fix the step count exactly. -/
theorem bound_trace_steps {p : Pins St} (h : BoundTrace ClearStep p) :
    p.steps = p.terminal.seq - p.initial.seq := by
  have := trace_seq h
  omega
#print axioms bound_trace_steps

/-- A verifier that checks `terminal.seq = initial.seq + k` accepts no trace of another length. -/
theorem fold_count_unique {s t : St} {n m : Nat}
    (hn : Trace ClearStep n s t) (hm : Trace ClearStep m s t) : n = m := by
  have a := trace_seq hn
  have b := trace_seq hm
  omega
#print axioms fold_count_unique

/-- Wrong count: a trace of length `n` cannot end where a trace of length `m ≠ n` ends. -/
theorem wrong_count_rejected {s t : St} {n m : Nat} (hne : n ≠ m)
    (hn : Trace ClearStep n s t) : ¬ Trace ClearStep m s t := by
  intro hm
  exact hne (fold_count_unique hn hm)
#print axioms wrong_count_rejected

/-- Genesis pin: a trace that starts at sequence zero ends at sequence `n`. -/
theorem genesis_pin {n : Nat} {s t : St} (h : Trace ClearStep n s t) (h0 : s.seq = 0) :
    t.seq = n := by
  have := trace_seq h
  omega
#print axioms genesis_pin

/-- The ledger identity is an invariant of every bound trace whose initial state satisfies it. -/
theorem bound_trace_identity {p : Pins St} (h : BoundTrace ClearStep p)
    (hi : ledgerIdentity p.initial.cash p.initial.claims p.initial.fund p.initial.carry
      p.initial.book) :
    ledgerIdentity p.terminal.cash p.terminal.claims p.terminal.fund p.terminal.carry
      p.terminal.book :=
  bound_trace_invariant
    (I := fun s => ledgerIdentity s.cash s.claims s.fund s.carry s.book)
    (fun _ _ hs hst => clearStep_identity hst hs) h hi
#print axioms bound_trace_identity

/-- The identity alone does not pin the initial state: a non-genesis initial state that
satisfies it yields a valid trace to a state that also satisfies it. -/
theorem nongenesis_trace_exists :
    ∃ s t : St, ledgerIdentity s.cash s.claims s.fund s.carry s.book ∧ s.seq ≠ 0 ∧
      ClearStep s t ∧ ledgerIdentity t.cash t.claims t.fund t.carry t.book := by
  let b : BatchAgg := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
  have hs : ledgerIdentity (100 : Int) 40 60 0 0 := by unfold ledgerIdentity; decide
  refine ⟨⟨7, 100, 40, 60, 0, 0⟩, stepApply ⟨7, 100, 40, 60, 0, 0⟩ b, hs, by decide, ⟨b, ?_, rfl⟩,
    batch_preserves_identity _ b hs⟩
  unfold Valid
  exact ⟨Nat.le_refl 0, by decide, by decide⟩
#print axioms nongenesis_trace_exists

/-! ## P3/P4: binding under an explicit collision-resistance hypothesis -/

/-- The collision-resistance premise for one hash on one pair of messages. It is a hypothesis
of the theorems below, never an axiom; computationally it is the event "the adversary has
not output a collision for this pair". -/
def NoCollisionAt {α β : Type} (H : α → β) (x y : α) : Prop := H x = H y → x = y

/-- Concatenation of fixed-width chunks. -/
def flat : List (List Nat) → List Nat
  | [] => []
  | r :: rs => r ++ flat rs

theorem flat_length (k : Nat) (xs : List (List Nat)) (h : ∀ r ∈ xs, r.length = k) :
    (flat xs).length = xs.length * k := by
  induction xs with
  | nil => simp [flat]
  | cons r rs ih =>
    have hr := h r (List.mem_cons_self ..)
    have := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [flat, List.length_append, List.length_cons, this, hr]
    rw [Nat.succ_mul]
    omega
#print axioms flat_length

theorem flat_inj (k : Nat) (xs ys : List (List Nat))
    (hx : ∀ r ∈ xs, r.length = k) (hy : ∀ r ∈ ys, r.length = k)
    (hl : xs.length = ys.length) (h : flat xs = flat ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons _ _ => simp only [List.length_nil, List.length_cons] at hl; omega
  | cons r rs ih =>
    cases ys with
    | nil => simp only [List.length_nil, List.length_cons] at hl; omega
    | cons r' rs' =>
      have hr := hx r (List.mem_cons_self ..)
      have hr' := hy r' (List.mem_cons_self ..)
      simp only [flat] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by omega)
      have := ih rs' (fun q hq => hx q (List.mem_cons_of_mem _ hq))
        (fun q hq => hy q (List.mem_cons_of_mem _ hq)) (by simp only [List.length_cons] at hl; omega) h2
      rw [h1, this]
#print axioms flat_inj

/-- Digest preimage of one batch (`clearing.rs:160-169`): row count, rows of width 12, claim
haircut count, entries of width 3, nine tail fields. -/
structure BatchPre where
  rows : List (List Nat)
  cuts : List (List Nat)
  tail : List Nat

def BatchPre.wf (b : BatchPre) : Prop :=
  (∀ r ∈ b.rows, r.length = 12) ∧ (∀ c ∈ b.cuts, c.length = 3) ∧ b.tail.length = 9

def BatchPre.enc (b : BatchPre) : List Nat :=
  b.rows.length :: (flat b.rows ++ (b.cuts.length :: (flat b.cuts ++ b.tail)))

theorem enc_inj (a b : BatchPre) (ha : a.wf) (hb : b.wf) (h : a.enc = b.enc) : a = b := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  obtain ⟨ar, ac, atl⟩ := a
  obtain ⟨br, bc, bt⟩ := b
  simp only [BatchPre.enc] at h
  simp only at a1 a2 a3 b1 b2 b3
  obtain ⟨hn, h⟩ := List.cons.inj h
  have l1 : (flat ar).length = (flat br).length := by
    rw [flat_length 12 ar a1, flat_length 12 br b1, hn]
  obtain ⟨hf, h⟩ := List.append_inj h l1
  obtain ⟨hm, h⟩ := List.cons.inj h
  have l2 : (flat ac).length = (flat bc).length := by
    rw [flat_length 3 ac a2, flat_length 3 bc b2, hm]
  obtain ⟨hg, ht⟩ := List.append_inj h l2
  have e1 := flat_inj 12 ar br a1 b1 hn hf
  have e2 := flat_inj 3 ac bc a2 b2 hm hg
  rw [e1, e2, ht]
#print axioms enc_inj

/-- P4: the tagged digest binds every row, claim haircut and tail field, given no collision on
the two preimages. This is the statement `C1` violated: it needs the digest to be computed from
the rows, which the circuit must enforce; the theorem is the specification it must meet. -/
theorem digest_binds_batch {D : Type} (H : List Nat → D) (a b : BatchPre) (ha : a.wf) (hb : b.wf)
    (hcr : NoCollisionAt H a.enc b.enc) (h : H a.enc = H b.enc) : a = b :=
  enc_inj a b ha hb (hcr h)
#print axioms digest_binds_batch

/-- Folded state vector of `clearing_step.rs:3-14`: five header fields, one claim per table
slot, three key limbs per slot, two chain limbs. -/
structure ZState where
  hdr : List Nat
  claims : List Nat
  keys : List Nat
  chain : List Nat

def ZState.wf (A : Nat) (z : ZState) : Prop :=
  z.hdr.length = 5 ∧ z.claims.length = A ∧ z.keys.length = 3 * A ∧ z.chain.length = 2

def ZState.enc (z : ZState) : List Nat := z.hdr ++ (z.claims ++ (z.keys ++ z.chain))

theorem zenc_inj (A : Nat) (a b : ZState) (ha : a.wf A) (hb : b.wf A) (h : a.enc = b.enc) :
    a = b := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  obtain ⟨ah, ac, ak, ach⟩ := a
  obtain ⟨bh, bc, bk, bch⟩ := b
  simp only [ZState.enc] at h
  simp only at a1 a2 a3 a4 b1 b2 b3 b4
  obtain ⟨e1, h⟩ := List.append_inj h (by omega)
  obtain ⟨e2, h⟩ := List.append_inj h (by omega)
  obtain ⟨e3, e4⟩ := List.append_inj h (by omega)
  rw [e1, e2, e3, e4]
#print axioms zenc_inj

/-- P3: the commitment over `z` binds every per-slot claim. Moving a claim from one account to
another changes `claims`, hence the encoding, hence the commitment, unless a collision is found. -/
theorem commitment_binds_claims {D : Type} (H : List Nat → D) (A : Nat) (a b : ZState)
    (ha : a.wf A) (hb : b.wf A) (hcr : NoCollisionAt H a.enc b.enc)
    (h : H a.enc = H b.enc) : a.claims = b.claims ∧ a.keys = b.keys ∧ a.hdr = b.hdr := by
  have := zenc_inj A a b ha hb (hcr h)
  subst this
  exact ⟨rfl, rfl, rfl⟩
#print axioms commitment_binds_claims

/-- Chain value after digests `d_0 .. d_{n-1}`, stored newest first: `c' = H(c, seq, d)`
(`clearing_step.rs:125-132`), `seq = seq0 + (number of earlier digests)`. -/
def chainR {D : Type} (H : D → Nat → D → D) (c0 : D) (seq0 : Nat) : List D → D
  | [] => c0
  | d :: rest => H (chainR H c0 seq0 rest) (seq0 + rest.length) d

/-- Hash of a triple is injective: the collision-resistance hypothesis of the chain theorem. -/
def CR3 {D : Type} (H : D → Nat → D → D) : Prop :=
  ∀ c s d c' s' d', H c s d = H c' s' d' → c = c' ∧ s = s' ∧ d = d'

/-- P4: under collision resistance, and with the genesis value outside the image of `H`, the
final chain value determines the whole digest sequence (hence its length). -/
theorem chain_binds_digests {D : Type} (H : D → Nat → D → D) (c0 : D) (seq0 : Nat)
    (hcr : CR3 H) (hz : ∀ c s d, H c s d ≠ c0) :
    ∀ ds ds' : List D, chainR H c0 seq0 ds = chainR H c0 seq0 ds' → ds = ds' := by
  intro ds
  induction ds with
  | nil =>
    intro ds' h
    cases ds' with
    | nil => rfl
    | cons d rest => exact absurd h.symm (hz _ _ _)
  | cons d rest ih =>
    intro ds' h
    cases ds' with
    | nil => exact absurd h (hz _ _ _)
    | cons d' rest' =>
      obtain ⟨h1, _, h3⟩ := hcr _ _ _ _ _ _ h
      rw [h3, ih rest' h1]
#print axioms chain_binds_digests

/-- Without the genesis premise a chain does not pin the sequence: if `c0` is itself an output
of `H`, the empty sequence and a one-element sequence share a chain value. -/
theorem chain_genesis_needed {D : Type} (H : D → Nat → D → D) (c0 : D) (seq0 : Nat) (d : D)
    (hc : H c0 seq0 d = c0) :
    chainR H c0 seq0 [d] = chainR H c0 seq0 [] ∧ [d] ≠ ([] : List D) := by
  refine ⟨?_, by simp⟩
  simpa [chainR] using hc
#print axioms chain_genesis_needed

/-! ## P7: Merkle inclusion binds the leaf under a pinned root -/

/-- Climb a path of `(is-right, sibling)` pairs from a leaf. -/
def climb {α : Type} (node : α → α → α) : α → List (Bool × α) → α
  | l, [] => l
  | l, (d, s) :: rest => climb node (if d then node s l else node l s) rest

def CRNode {α : Type} (node : α → α → α) : Prop :=
  ∀ a b c d, node a b = node c d → a = c ∧ b = d

theorem climb_binds {α : Type} (node : α → α → α) (hcr : CRNode node) :
    ∀ (p p' : List (Bool × α)) (l l' : α), p.map Prod.fst = p'.map Prod.fst →
      climb node l p = climb node l' p' → l = l' ∧ p = p' := by
  intro p
  induction p with
  | nil =>
    intro p' l l' hd h
    cases p' with
    | nil => exact ⟨h, rfl⟩
    | cons _ _ => simp at hd
  | cons x rest ih =>
    intro p' l l' hd h
    cases p' with
    | nil => simp at hd
    | cons x' rest' =>
      obtain ⟨d, s⟩ := x
      obtain ⟨d', s'⟩ := x'
      simp only [List.map, List.cons.injEq] at hd
      obtain ⟨hd1, hd2⟩ := hd
      simp only [climb] at h
      obtain ⟨hn, hp⟩ := ih rest' _ _ hd2 h
      subst hd1
      have hp' : rest = rest' := hp
      subst hp'
      cases d
      · simp only [Bool.false_eq_true, if_false] at hn
        obtain ⟨e1, e2⟩ := hcr _ _ _ _ hn
        subst e1; subst e2
        exact ⟨rfl, rfl⟩
      · simp only [if_true] at hn
        obtain ⟨e1, e2⟩ := hcr _ _ _ _ hn
        subst e1; subst e2
        exact ⟨rfl, rfl⟩
#print axioms climb_binds

/-- P7: if the circuit's computed root equals the pinned root and the position (directions) is the
same, the opened leaf is the authentic leaf: a forged price record cannot be opened. -/
theorem oracle_leaf_bound {α : Type} (node : α → α → α) (hcr : CRNode node)
    (authentic forged : α) (pa pf : List (Bool × α))
    (hpos : pa.map Prod.fst = pf.map Prod.fst)
    (hroot : climb node authentic pa = climb node forged pf) : authentic = forged :=
  (climb_binds node hcr pa pf authentic forged hpos hroot).1
#print axioms oracle_leaf_bound

/-! ## P6: nullifier uniqueness and replay -/

/-- Spend relation over a list of already-spent nullifiers. -/
def accept {N : Type} [DecidableEq N] (spent : List N) (n : N) : Option (List N) :=
  if n ∈ spent then none else some (n :: spent)

theorem accept_replay {N : Type} [DecidableEq N] (spent : List N) (n : N) (h : n ∈ spent) :
    accept spent n = none := by
  simp [accept, h]
#print axioms accept_replay

theorem accept_nodup {N : Type} [DecidableEq N] {spent spent' : List N} {n : N}
    (hnd : spent.Nodup) (h : accept spent n = some spent') : spent'.Nodup := by
  unfold accept at h
  by_cases hm : n ∈ spent
  · simp [hm] at h
  · simp only [hm, if_false, Option.some.injEq] at h
    subst h
    exact List.nodup_cons.mpr ⟨hm, hnd⟩
#print axioms accept_nodup

/-- Run a list of nullifiers through the transition. -/
def runAll {N : Type} [DecidableEq N] : List N → List N → Option (List N)
  | spent, [] => some spent
  | spent, n :: ns =>
    match accept spent n with
    | none => none
    | some s => runAll s ns

theorem runAll_inter_none {N : Type} [DecidableEq N] :
    ∀ (ns spent : List N), (∃ n, n ∈ ns ∧ n ∈ spent) → runAll spent ns = none := by
  intro ns
  induction ns with
  | nil => rintro spent ⟨n, hn, _⟩; simp at hn
  | cons m ms ih =>
    rintro spent ⟨n, hn, hs⟩
    by_cases hm : m ∈ spent
    · simp [runAll, accept, hm]
    · simp only [runAll, accept, hm, if_false]
      apply ih
      refine ⟨n, ?_, List.mem_cons_of_mem _ hs⟩
      rcases List.mem_cons.mp hn with rfl | hn'
      · exact absurd hs hm
      · exact hn'
#print axioms runAll_inter_none

/-- No replay: a list that contains a repeat is rejected by the state transition. -/
theorem runAll_rejects_repeat {N : Type} [DecidableEq N] :
    ∀ (ns spent : List N), ¬ ns.Nodup → runAll spent ns = none := by
  intro ns
  induction ns with
  | nil => intro spent h; exact absurd List.nodup_nil h
  | cons n ns ih =>
    intro spent h
    by_cases hm : n ∈ spent
    · simp [runAll, accept, hm]
    · simp only [runAll, accept, hm, if_false]
      by_cases hnm : n ∈ ns
      · exact runAll_inter_none ns (n :: spent) ⟨n, hnm, List.mem_cons_self ..⟩
      · exact ih _ (fun hn => h (List.nodup_cons.mpr ⟨hnm, hn⟩))
#print axioms runAll_rejects_repeat

/-- A nullifier already spent is rejected when it reappears in a later list. -/
theorem runAll_rejects_spent {N : Type} [DecidableEq N] (spent ns : List N) (n : N)
    (hs : n ∈ spent) (hn : n ∈ ns) : runAll spent ns = none :=
  runAll_inter_none ns spent ⟨n, hn, hs⟩
#print axioms runAll_rejects_spent

/-- A successful run accepted a Nodup list, none of it spent before. -/
theorem runAll_some_nodup {N : Type} [DecidableEq N] {ns spent s : List N}
    (h : runAll spent ns = some s) : ns.Nodup := by
  by_cases hc : ns.Nodup
  · exact hc
  · rw [runAll_rejects_repeat ns spent hc] at h
    cases h
#print axioms runAll_some_nodup

/-- Slot insertion as in `unified_batch_circuit.rs:151-168`: only slot emptiness is checked. -/
def slotInsert (t : Nat → Option Nat) (i n : Nat) : Option (Nat → Option Nat) :=
  if t i = none then some (fun j => if j = i then some n else t j) else none

/-- The slot rule alone does not give nullifier uniqueness: one nullifier occupies two slots. -/
theorem slot_allows_duplicate :
    ∃ t1 t2, slotInsert (fun _ => none) 0 5 = some t1 ∧ slotInsert t1 1 5 = some t2 ∧
      t2 0 = some 5 ∧ t2 1 = some 5 := by
  refine ⟨fun j => if j = 0 then some 5 else none,
    fun j => if j = 1 then some 5 else if j = 0 then some 5 else none, ?_, ?_, ?_, ?_⟩
  · simp [slotInsert]
  · simp only [slotInsert]
    rw [if_pos (by simp)]
  · simp
  · simp
#print axioms slot_allows_duplicate

/-! ## P8: canonical encoding and field-wrap exclusion -/

/-- BN254 scalar field modulus (the field of the Nova primary circuit). -/
def bn254 : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- Value of little-endian limbs of `w` bits. -/
def limbVal (w : Nat) : List Nat → Nat
  | [] => 0
  | l :: ls => l + 2 ^ w * limbVal w ls

theorem limbVal_lt (w : Nat) (ls : List Nat) (h : ∀ l ∈ ls, l < 2 ^ w) :
    limbVal w ls < 2 ^ (w * ls.length) := by
  induction ls with
  | nil => simp [limbVal]
  | cons l ls ih =>
    have hl := h l (List.mem_cons_self ..)
    have hv := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h1 : 2 ^ w * (limbVal w ls + 1) ≤ 2 ^ w * 2 ^ (w * ls.length) :=
      Nat.mul_le_mul_left _ hv
    have h2 : 2 ^ (w * (ls.length + 1)) = 2 ^ w * 2 ^ (w * ls.length) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    simp only [limbVal, List.length_cons]
    rw [Nat.mul_add, Nat.mul_one] at h1
    rw [h2]
    omega
#print axioms limbVal_lt

theorem limbVal_inj (w : Nat) :
    ∀ (ls ls' : List Nat), (∀ l ∈ ls, l < 2 ^ w) → (∀ l ∈ ls', l < 2 ^ w) →
      ls.length = ls'.length → limbVal w ls = limbVal w ls' → ls = ls' := by
  intro ls
  induction ls with
  | nil =>
    intro ls' _ _ hl _
    cases ls' with
    | nil => rfl
    | cons _ _ => simp only [List.length_nil, List.length_cons] at hl; omega
  | cons l ls ih =>
    intro ls' h h' hl hv
    cases ls' with
    | nil => simp only [List.length_nil, List.length_cons] at hl; omega
    | cons l' ls' =>
      have hX : 0 < 2 ^ w := Nat.two_pow_pos w
      have hl1 := h l (List.mem_cons_self ..)
      have hl2 := h' l' (List.mem_cons_self ..)
      simp only [limbVal] at hv
      have e1 : l = l' := by
        have a1 : (l + 2 ^ w * limbVal w ls) % 2 ^ w = l := by
          rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hl1
        have a2 : (l' + 2 ^ w * limbVal w ls') % 2 ^ w = l' := by
          rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hl2
        rw [← a1, ← a2, hv]
      subst e1
      have e2 : limbVal w ls = limbVal w ls' := Nat.eq_of_mul_eq_mul_left hX (by omega)
      have := ih ls' (fun q hq => h q (List.mem_cons_of_mem _ hq))
        (fun q hq => h' q (List.mem_cons_of_mem _ hq))
        (by simp only [List.length_cons] at hl; omega) e2
      rw [this]
#print axioms limbVal_inj

theorem two64_lt_bn254 : 2 ^ 64 < bn254 := by unfold bn254; decide
#print axioms two64_lt_bn254

/-- Limbs bounded in range, total width below the modulus: equal residues are equal integers.
This is the no-wrap hypothesis a circuit must establish with its range checks. -/
theorem limbs_no_wrap (p w : Nat) (ls ls' : List Nat)
    (h : ∀ l ∈ ls, l < 2 ^ w) (h' : ∀ l ∈ ls', l < 2 ^ w)
    (hp : 2 ^ (w * ls.length) ≤ p) (hp' : 2 ^ (w * ls'.length) ≤ p)
    (heq : limbVal w ls % p = limbVal w ls' % p) : limbVal w ls = limbVal w ls' :=
  no_wrap_eq p _ _ (Nat.lt_of_lt_of_le (limbVal_lt w ls h) hp)
    (Nat.lt_of_lt_of_le (limbVal_lt w ls' h') hp') heq
#print axioms limbs_no_wrap

/-- Four 64-bit limbs (a 256-bit value) are not wrap-free modulo BN254: the bound fails. -/
theorem four_limbs_wrap : ¬ (2 ^ (64 * 4) ≤ bn254) := by
  unfold bn254; decide
#print axioms four_limbs_wrap

/-- Two 64-bit limbs are wrap-free modulo BN254. -/
theorem two_limbs_fit : 2 ^ (64 * 2) ≤ bn254 := by
  unfold bn254; decide
#print axioms two_limbs_fit

/-- Counterexample without the bound: `p + k` and `k` agree modulo `p` and differ as integers. -/
theorem wrap_counterexample (k : Nat) :
    (bn254 + k) % bn254 = k % bn254 ∧ bn254 + k ≠ k := by
  refine ⟨Nat.add_mod_left bn254 k, ?_⟩
  unfold bn254; omega
#print axioms wrap_counterexample

/-- The same value is outside every 64-bit range, so a range check rejects it. -/
theorem wrap_value_out_of_range (k : Nat) : ¬ (bn254 + k < 2 ^ 64) := by
  have := two64_lt_bn254
  omega
#print axioms wrap_value_out_of_range

/-- Integer identity from field identity: a difference below the modulus in absolute value
and divisible by it is zero. -/
theorem int_identity_no_wrap (x : Int) (h : x % (bn254 : Int) = 0)
    (hb : -(bn254 : Int) < x ∧ x < (bn254 : Int)) : x = 0 := by
  have hp : (bn254 : Int) = 21888242871839275222246405745257275088548364400416034343698204186575808495617 := rfl
  rw [hp] at h hb
  omega
#print axioms int_identity_no_wrap

/-- Two's-complement 64-bit encoding is injective on its range. -/
theorem i64_wrap_free (a b : Int) (ha : -9223372036854775808 ≤ a ∧ a < 9223372036854775808)
    (hb : -9223372036854775808 ≤ b ∧ b < 9223372036854775808)
    (h : a % 18446744073709551616 = b % 18446744073709551616) : a = b := by
  omega
#print axioms i64_wrap_free

/-- Without the signed range the 64-bit residues of `2^63` and `-2^63` coincide. -/
theorem i64_wrap_counterexample :
    (9223372036854775808 : Int) % 18446744073709551616
      = (-9223372036854775808 : Int) % 18446744073709551616 ∧
    (9223372036854775808 : Int) ≠ -9223372036854775808 := by
  constructor <;> decide
#print axioms i64_wrap_counterexample

/-- Fixed-width little-endian bytes. -/
def toLE : Nat → Nat → List Nat
  | 0, _ => []
  | w + 1, n => n % 256 :: toLE w (n / 256)

def ofLE : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * ofLE bs

theorem ofLE_toLE : ∀ (w n : Nat), n < 256 ^ w → ofLE (toLE w n) = n := by
  intro w
  induction w with
  | zero =>
    intro n h
    rw [Nat.pow_zero] at h
    have : n = 0 := by omega
    subst this
    rfl
  | succ w ih =>
    intro n h
    have h1 : n / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at h
      omega
    simp only [toLE, ofLE, ih _ h1]
    omega
#print axioms ofLE_toLE

/-- Canonical encoding: two in-range values with the same fixed-width bytes are equal. -/
theorem toLE_inj (w a b : Nat) (ha : a < 256 ^ w) (hb : b < 256 ^ w)
    (h : toLE w a = toLE w b) : a = b := by
  rw [← ofLE_toLE w a ha, ← ofLE_toLE w b hb, h]
#print axioms toLE_inj

/-- Bytes of a valid encoding are in range, and the encoding is unique per value. -/
theorem toLE_length (w n : Nat) : (toLE w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toLE, ih]
#print axioms toLE_length

end MathCan.ZKLean.Settlement

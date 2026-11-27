import Std
import Lean

/-! ZKL-01/03/04/05/06/07. Core-only Lean development.
The modular evaluator is an independent semantics for canonical R1CS exports.
Primality, exporter identity, Rust refinement and cryptographic soundness are
separate obligations. No axioms or sorry declarations are introduced here. -/
namespace MathCan.ZKLean

structure Term where
  wire : Nat
  coeff : Nat
  deriving DecidableEq, Repr

abbrev LC := List Term
abbrev Assignment := Nat → Nat

structure Row where
  a : LC
  b : LC
  c : LC
  deriving DecidableEq, Repr

structure Shape where
  modulus : Nat
  wires : Nat
  publicWires : List Nat
  rows : List Row
  deriving Repr

def evalLC (p : Nat) (w : Assignment) (l : LC) : Nat :=
  (l.foldl (fun acc t => acc + t.coeff * w t.wire) 0) % p

def rowHolds (p : Nat) (w : Assignment) (r : Row) : Prop :=
  (evalLC p w r.a * evalLC p w r.b) % p = evalLC p w r.c

def wellFormed (s : Shape) : Prop :=
  1 < s.modulus ∧ 0 < s.wires ∧
  (∀ i ∈ s.publicWires, 0 < i ∧ i < s.wires) ∧
  s.publicWires.Nodup ∧
  (∀ r ∈ s.rows, ∀ t ∈ r.a ++ r.b ++ r.c,
    t.wire < s.wires ∧ t.coeff < s.modulus)

def validAssignment (s : Shape) (w : Assignment) : Prop :=
  w 0 = 1 ∧ ∀ i, i < s.wires → w i < s.modulus

def holds (p : Nat) (w : Assignment) (rows : List Row) : Prop :=
  ∀ r ∈ rows, rowHolds p w r

def accepts (s : Shape) (x : List Nat) : Prop :=
  wellFormed s ∧ ∃ w : Assignment,
    validAssignment s w ∧ s.publicWires.map w = x ∧ holds s.modulus w s.rows

theorem holds_append (p : Nat) (w : Assignment) (a b : List Row) :
    holds p w (a ++ b) ↔ holds p w a ∧ holds p w b := by
  constructor
  · intro h
    exact ⟨fun r hr => h r (List.mem_append.mpr (Or.inl hr)),
           fun r hr => h r (List.mem_append.mpr (Or.inr hr))⟩
  · intro h r hr
    rcases List.mem_append.mp hr with ha | hb
    · exact h.1 r ha
    · exact h.2 r hb

theorem redundant_row (p : Nat) (rs : List Row) (r : Row)
    (h : ∀ w, holds p w rs → rowHolds p w r) (w : Assignment) :
    holds p w (r :: rs) ↔ holds p w rs := by
  constructor
  · intro ha q hq
    exact ha q (List.mem_cons.mpr (Or.inr hq))
  · intro ha q hq
    rcases List.mem_cons.mp hq with he | ht
    · subst q
      exact h w ha
    · exact ha q ht

abbrev Rel (X Y : Type) := X → Y → Prop
def denotation {X Y W : Type} (c : X → Y → W → Prop) : Rel X Y :=
  fun x y => ∃ w, c x y w

def refines {X Y : Type} (r s : Rel X Y) : Prop :=
  ∀ x y, r x y → s x y

def equivalent {X Y : Type} (r s : Rel X Y) : Prop :=
  ∀ x y, r x y ↔ s x y

def compose {X Y Z : Type} (r : Rel X Y) (s : Rel Y Z) : Rel X Z :=
  fun x z => ∃ y, r x y ∧ s y z

theorem compose_refines {X Y Z : Type} {a a' : Rel X Y} {b b' : Rel Y Z}
    (ha : refines a a') (hb : refines b b') :
    refines (compose a b) (compose a' b') := by
  intro x z h
  rcases h with ⟨y, hy, hz⟩
  exact ⟨y, ha x y hy, hb y z hz⟩

theorem compose_equivalent {X Y Z : Type} {a a' : Rel X Y} {b b' : Rel Y Z}
    (ha : equivalent a a') (hb : equivalent b b') :
    equivalent (compose a b) (compose a' b') := by
  intro x z
  constructor
  · exact compose_refines (fun x y => (ha x y).mp) (fun y z => (hb y z).mp) x z
  · exact compose_refines (fun x y => (ha x y).mpr) (fun y z => (hb y z).mpr) x z

theorem optimization_transport {X Y : Type} {c c' s : Rel X Y}
    (h : equivalent c' c) (hs : equivalent c s) : equivalent c' s :=
  fun x y => (h x y).trans (hs x y)

/- Arithmetic lifting: these are integer-level gadget obligations. The concrete
   R1CS encoding must establish the hypotheses, including no field wrap. -/
theorem no_wrap_eq (p a b : Nat) (ha : a < p) (hb : b < p)
    (h : a % p = b % p) : a = b := by
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h

def rangeSpec (bits x : Nat) : Prop := x < 2 ^ bits

theorem range_weaken (bits x y : Nat) (hx : rangeSpec bits x) (h : y ≤ x) :
    rangeSpec bits y := by
  exact Nat.lt_of_le_of_lt h hx

def minSpec (a b m : Nat) : Prop := m ≤ a ∧ m ≤ b ∧ (m = a ∨ m = b)

theorem minSpec_exact (a b m : Nat) (h : minSpec a b m) :
    m = min a b := by
  rcases h with ⟨ha, hb, he | he⟩
  · subst m
    exact (Nat.min_eq_left hb).symm
  · subst m
    exact (Nat.min_eq_right ha).symm

def divSpec (n d q r : Nat) : Prop := 0 < d ∧ n = q * d + r ∧ r < d

theorem divSpec_unique (n d q r q' r' : Nat)
    (h : divSpec n d q r) (h' : divSpec n d q' r') : q = q' ∧ r = r' := by
  rcases h with ⟨hd, hn, hr⟩
  rcases h' with ⟨_, hn', hr'⟩
  have hq : q = q' := by
    by_contra hne
    have hor : q < q' ∨ q' < q := by omega
    rcases hor with hlt | hlt
    · have hs : q + 1 ≤ q' := by omega
      have hm := Nat.mul_le_mul_right d hs
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
    · have hs : q' + 1 ≤ q := by omega
      have hm := Nat.mul_le_mul_right d hs
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
  subst q'
  exact ⟨rfl, by omega⟩

/- V3 local waterfall: loss collection, own claim, fund, haircut and carry.
   Full batch ordering, claim-map, signed PnL, pro-rata and digests remain open. -/
structure Loss where
  collected : Nat
  own : Nat
  shortfall : Nat
  deriving DecidableEq, Repr

def collectLoss (need released claim : Nat) : Loss :=
  let c := min need released
  let o := min (need - c) claim
  ⟨c, o, need - c - o⟩

theorem collectLoss_conserves (need released claim : Nat) :
    let l := collectLoss need released claim
    l.collected + l.own + l.shortfall = need := by
  change min need released + min (need - min need released) claim +
    (need - min need released - min (need - min need released) claim) = need
  have hc := Nat.min_le_left need released
  have ho := Nat.min_le_left (need - min need released) claim
  omega

theorem collectLoss_priority (need released claim : Nat) :
    let l := collectLoss need released claim
    l.collected = min need released ∧
      l.own = min (need - l.collected) claim := by
  exact ⟨rfl, rfl⟩

structure Waterfall where
  fundUsed : Nat
  haircut : Nat
  carry : Nat
  deriving Repr

def allocateDefault (shortfall fund carry base : Nat) : Waterfall :=
  let f := min shortfall fund
  let owed := shortfall - f + carry
  let h := min owed base
  ⟨f, h, owed - h⟩

theorem allocateDefault_conserves (shortfall fund carry base : Nat) :
    let w := allocateDefault shortfall fund carry base
    w.fundUsed + w.haircut + w.carry = shortfall + carry := by
  change min shortfall fund + min (shortfall - min shortfall fund + carry) base +
    (shortfall - min shortfall fund + carry -
      min (shortfall - min shortfall fund + carry) base) = shortfall + carry
  have hf := Nat.min_le_left shortfall fund
  have hh := Nat.min_le_left (shortfall - min shortfall fund + carry) base
  omega

def cashStep (cash : Int) (collected paid : Nat) : Int :=
  cash + (collected : Int) - (paid : Int)

theorem net_conservation (cash : Int) (collected paid : Nat) :
    ((paid : Int) - (collected : Int)) +
      (cashStep cash collected paid - cash) = 0 := by
  unfold cashStep
  omega

theorem cash_floor (cash : Int) (collected paid : Nat)
    (h : (paid : Int) ≤ max (cash + (collected : Int)) 0) :
    min cash 0 ≤ cashStep cash collected paid := by
  unfold cashStep
  omega

/- Recursive safety for a specified transition. In an actual proof this must
   be connected to the verifier by a separate cryptographic refinement. -/
inductive Trace {S : Type} (step : Rel S S) : Nat → S → S → Prop where
  | nil (s : S) : Trace step 0 s s
  | snoc {n : Nat} {s t u : S} : Trace step n s t → step t u → Trace step (n+1) s u

theorem trace_invariant {S : Type} {step : Rel S S} {I : S → Prop}
    (preserve : ∀ s t, I s → step s t → I t)
    {n : Nat} {s t : S} (h : Trace step n s t) (hs : I s) : I t := by
  induction h with
  | nil => exact hs
  | snoc _ hstep ih => exact preserve _ _ ih hstep

structure Pins (S : Type) where
  initial : S
  terminal : S
  steps : Nat

def BoundTrace {S : Type} (step : Rel S S) (p : Pins S) : Prop :=
  Trace step p.steps p.initial p.terminal

theorem bound_trace_invariant {S : Type} {step : Rel S S} {I : S → Prop}
    (preserve : ∀ s t, I s → step s t → I t) {p : Pins S}
    (h : BoundTrace step p) (hi : I p.initial) : I p.terminal :=
  trace_invariant preserve h hi

-- Exact byte-width ledger for UtxoRefL2SettlementStatementV0 (half-open offsets).
def statementWidths : List Nat := [33,2,1,32,32,32,32,32,32,32,32,8,4]
theorem statement_width : statementWidths.foldl Nat.add 0 = 304 := by decide

-- Collision resistance is an explicit computational premise, not an injectivity theorem.
end MathCan.ZKLean

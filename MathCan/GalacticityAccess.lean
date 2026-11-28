import Lean

namespace GalacticityAccess

/-- Adaptive entry queries with arbitrary output (e.g. a factorization). -/
inductive EntryTree (Q O : Type) where
  | leaf : O → EntryTree Q O
  | ask : Q → EntryTree Q O → EntryTree Q O → EntryTree Q O

def EntryTree.run {Q O : Type} (o : Q → Bool) : EntryTree Q O → O
  | .leaf v => v
  | .ask q l r => if o q then run o r else run o l

def EntryTree.path {Q O : Type} (o : Q → Bool) : EntryTree Q O → List Q
  | .leaf _ => []
  | .ask q l r => q :: (if o q then path o r else path o l)

theorem same_path_run {Q O : Type} (o o' : Q → Bool) (tree : EntryTree Q O)
    (h : ∀ q, q ∈ tree.path o → o' q = o q) :
    tree.run o' = tree.run o := by
  induction tree with
  | leaf v => rfl
  | ask q l r ihl ihr =>
    have hq : o' q = o q := h q (by simp [EntryTree.path])
    cases e : o q with
    | false =>
      have hl : ∀ a, a ∈ l.path o → o' a = o a := by
        intro a ha
        apply h a
        simp [EntryTree.path, e, ha]
      simp [EntryTree.run, hq, e, ihl hl]
    | true =>
      have hr : ∀ a, a ∈ r.path o → o' a = o a := by
        intro a ha
        apply h a
        simp [EntryTree.path, e, ha]
      simp [EntryTree.run, hq, e, ihr hr]

def zeroOracle {Q : Type} : Q → Bool := fun _ => false
def spikeOracle {Q : Type} [DecidableEq Q] (i : Q) : Q → Bool :=
  fun q => decide (q = i)

/-- Flipping an unread coordinate preserves the all-zero path output. -/
theorem unread_spike {Q O : Type} [DecidableEq Q]
    (tree : EntryTree Q O) (i : Q)
    (h : i ∉ tree.path zeroOracle) :
    tree.run (spikeOracle i) = tree.run zeroOracle := by
  apply same_path_run zeroOracle (spikeOracle i) tree
  intro q hq
  have hn : q ≠ i := by
    intro e
    subst q
    exact h hq
  simp [spikeOracle, zeroOracle, hn]

/-- Exact rejection of every single-entry spike forces every coordinate
    onto the all-zero transcript of a zero-certificate verifier. -/
theorem zero_certificate_reads_all {Q : Type} [DecidableEq Q]
    (tree : EntryTree Q Bool)
    (hz : tree.run zeroOracle = true)
    (hs : ∀ i, tree.run (spikeOracle i) = false)
    (i : Q) : i ∈ tree.path zeroOracle := by
  by_cases h : i ∈ tree.path zeroOracle
  · exact h
  · have e := unread_spike tree i h
    rw [hz, hs i] at e
    contradiction

/-- With exactly one spike promised, the all-zero transcript can omit
    at most one coordinate if the output identifies the spike. -/
theorem exact_spike_at_most_one_missing {Q : Type} [DecidableEq Q]
    (tree : EntryTree Q Q)
    (correct : ∀ i, tree.run (spikeOracle i) = i)
    (i j : Q) (hi : i ∉ tree.path zeroOracle)
    (hj : j ∉ tree.path zeroOracle) : i = j := by
  have ei := unread_spike tree i hi
  have ej := unread_spike tree j hj
  rw [correct i] at ei
  rw [correct j] at ej
  exact ei.trans ej.symm

/-- Positive setup cannot be recovered if target-scaled marginal cost
    is already at least the baseline marginal cost. -/
theorem no_break_even_at_ceiling (C u v m : Nat)
    (hC : 0 < C) (h : u ≤ v) :
    ¬ C + m * v ≤ m * u := by
  have hm : m * u ≤ m * v := Nat.mul_le_mul_left m h
  omega

/-- If shared per-use work is charged equally, absolute savings are
    preserved even though the attainable multiplicative gain changes. -/
theorem shared_work_cancel (a b s : Nat) :
    a + s ≤ b + s ↔ a ≤ b := by omega

end GalacticityAccess

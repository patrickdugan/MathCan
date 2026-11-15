import MathCan.SpatialRouting

/-!
The normalized, bounded-gate snake from the spatial construction. Parity is
read by the explicit ReLU table, rather than assumed to be an oracle. The
final theorem composes safe-cell inequalities, address extraction, parity,
rank, and exact capture of all jet coordinates.
-/
namespace MathCan.SpatialNormalized
open Std Lean.Grind MathCan.SpatialScalar MathCan.SpatialRouting
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast

def normalizedStep (K B : Nat) (i b q : R) : R :=
  i/(K:R) + (q + gate 2 b (1 - 1/(B:R) - 2*q))/(K:R)

theorem normalized_step_exact (K B i r : Nat) (hK : 0 < K) (hr : r < B) :
    normalizedStep K B (i:R) (if i % 2 = 0 then 0 else 1) ((r:R)/(B:R)) =
      ((if i % 2 = 0 then i*B+r else i*B+(B-1-r):Nat):R)/((K*B:Nat):R) := by
  have hB : 0 < (B:R) := OrderedRing.pos_natCast_of_pos B (by omega)
  have hKn : (K:R) ≠ 0 := by
    have := OrderedRing.pos_natCast_of_pos (R := R) K hK
    grind
  have hBn : (B:R) ≠ 0 := by grind
  have hinv : 0 ≤ (B:R)⁻¹ := Preorder.le_of_lt (Field.IsOrdered.inv_pos_iff.mpr hB)
  have hr0 : 0 ≤ (r:R) := OrderedRing.natCast_nonneg
  have hq0 := OrderedRing.mul_nonneg hr0 hinv
  have hle := OrderedRing.natCast_le_natCast_of_le (R := R) (r+1) B (by omega)
  simp only [Semiring.natCast_succ] at hle
  have hq := OrderedRing.mul_le_mul_of_nonneg_right hle hinv
  rw [Semiring.right_distrib, Semiring.one_mul, Field.mul_inv_cancel hBn] at hq
  have hBinv := Field.mul_inv_cancel hBn
  have hKinv := Field.mul_inv_cancel hKn
  have hs : r+(B-1-r)+1 = B := by omega
  have hsR := congrArg (fun n : Nat => (n:R)) hs
  simp only [Semiring.natCast_add, Semiring.natCast_one] at hsR
  unfold normalizedStep
  simp only [Field.div_eq_mul_inv, Semiring.one_mul]
  by_cases h : i % 2 = 0
  · rw [if_pos h, if_pos h, gate_zero]
    simp only [Semiring.natCast_add, Semiring.natCast_mul, Field.inv_mul]
    grind
  · rw [if_neg h, if_neg h, gate_one _ _ (by constructor <;> grind)]
    simp only [Semiring.natCast_add, Semiring.natCast_mul, Field.inv_mul]
    grind

def normalizedCircuit (K : Nat) : List R → R
  | [] => 0
  | i :: tail => normalizedStep K (K^tail.length) i
      (lookup K (fun j => if j % 2 = 0 then 0 else 1) i)
      (normalizedCircuit K tail)

/-- The actual scalar parity table and bounded gate compute rank divided by B. -/
theorem normalized_circuit_exact (K : Nat) (hK : 0 < K) (digits : List Nat)
    (valid : ∀ i, i ∈ digits → i < K) :
    normalizedCircuit K (digits.map (fun i : Nat => (i:R))) =
      (snakeRank K digits:R)/((K^digits.length:Nat):R) := by
  induction digits with
  | nil => simp [normalizedCircuit, snakeRank, Field.div_eq_mul_inv, Semiring.zero_mul,
      Semiring.natCast_zero]
  | cons i tail ih =>
    have hi := valid i (by simp)
    have ht : ∀ j, j ∈ tail → j < K := by
      intro j hj
      exact valid j (by simp [hj])
    simp only [List.map_cons, normalizedCircuit, List.length_map]
    rw [lookup_at_index K i hi, ih ht]
    simpa only [snakeRank, List.length_cons, Nat.pow_succ'] using
      normalized_step_exact K (K^tail.length) i (snakeRank K tail)
        hK (snake_rank_bound K hK tail ht)

structure Site (R : Type u) where
  coarse : Nat
  fine : Nat
  position : R

def decodedDigits (n K : Nat) (delta : R) (sites : List (Site R)) : List R :=
  sites.map fun s => fineAddress K delta
    (s.position - coarseAddress n K delta s.position * (K:R))

def validSites (n K : Nat) (delta : R) (sites : List (Site R)) : Prop :=
  ∀ s, s ∈ sites → s.coarse ≤ n ∧ s.fine < K ∧
    safeCell delta s.position (s.coarse*K+s.fine)

theorem decoded_digits_exact (n K : Nat) (delta : R) (hd : 0 < delta)
    (sites : List (Site R)) (valid : validSites n K delta sites) :
    decodedDigits n K delta sites = sites.map (fun s => (s.fine:R)) := by
  induction sites with
  | nil => rfl
  | cons s tail ih =>
    have hs := valid s (by simp)
    have ht : validSites n K delta tail := by
      intro t hmem
      exact valid t (by simp [hmem])
    simp only [decodedDigits, List.map_cons] at ih ⊢
    rw [(spatial_address n K s.coarse s.fine hs.1 hs.2.1 delta s.position hd hs.2.2).2,
      ih ht]

/-- From geometric safe-cell inequalities to the selected vector of jets. -/
theorem safe_spatial_capture (n K J : Nat) (hK : 0 < K) (delta : R) (hd : 0 < delta)
    (sites : List (Site R)) (valid : validSites n K delta sites) (C : R)
    (jets : Nat → Fin J → R)
    (bounds : ∀ j, j < K^sites.length → ∀ beta, -C ≤ jets j beta ∧ jets j beta ≤ C) :
    (fun beta => sum (K^sites.length) (fun j => gate C
      (triangle (j:R) (((K^sites.length:Nat):R) * normalizedCircuit K (decodedDigits n K delta sites)))
      (jets j beta))) = jets (snakeRank K (sites.map Site.fine)) := by
  have hvalid : ∀ i, i ∈ sites.map Site.fine → i < K := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨s, hs, he⟩
    subst i
    exact (valid s hs).2.1
  rw [decoded_digits_exact n K delta hd sites valid]
  have heq : sites.map (fun s => (s.fine:R)) =
      (sites.map Site.fine).map (fun i : Nat => (i:R)) := by simp [List.map_map]
  rw [heq, normalized_circuit_exact K hK _ hvalid]
  simp only [List.length_map]
  have hBn : ((K^sites.length:Nat):R) ≠ 0 := by
    have := OrderedRing.pos_natCast_of_pos (R := R) (K^sites.length) (Nat.pow_pos hK)
    grind
  rw [CommSemiring.mul_comm ((K^sites.length:Nat):R), Field.div_mul_cancel hBn]
  apply capture_vector
  · simpa only [List.length_map] using snake_rank_bound K hK (sites.map Site.fine) hvalid
  · exact bounds

end MathCan.SpatialNormalized

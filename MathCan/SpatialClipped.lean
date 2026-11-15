import MathCan.SpatialNormalized

/-! Clipped capture registers are bounded for every input, and preserve the
exact selected jet on safe cells. This is a scalar semantics theorem; it does
not count wires or replace the still-required dense-network compiler proof. -/
namespace MathCan.SpatialClipped
open Std Lean.Grind MathCan.SpatialScalar MathCan.SpatialRouting MathCan.SpatialNormalized
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast

theorem normalized_rank_range (K : Nat) (hK : 0 < K) (digits : List Nat)
    (valid : ∀ i, i ∈ digits → i < K) :
    0 ≤ (snakeRank K digits:R)/((K^digits.length:Nat):R) ∧
    (snakeRank K digits:R)/((K^digits.length:Nat):R) ≤ 1 := by
  have hB := OrderedRing.pos_natCast_of_pos (R := R) (K^digits.length) (Nat.pow_pos hK)
  have hBn : ((K^digits.length:Nat):R) ≠ 0 := by grind
  have hinv := Preorder.le_of_lt (Field.IsOrdered.inv_pos_iff.mpr hB)
  have hr0 : 0 ≤ (snakeRank K digits:R) := OrderedRing.natCast_nonneg
  have hle := OrderedRing.natCast_le_natCast_of_le (R := R) (snakeRank K digits)
    (K^digits.length) (Nat.le_of_lt (snake_rank_bound K hK digits valid))
  have hm := OrderedRing.mul_le_mul_of_nonneg_right hle hinv
  rw [Field.mul_inv_cancel hBn] at hm
  simp only [Field.div_eq_mul_inv]
  exact ⟨OrderedRing.mul_nonneg hr0 hinv, hm⟩

def clippedCircuit (K : Nat) : List R → R
  | [] => 0
  | i :: tail => clip 1 (normalizedStep K (K^tail.length) i
      (lookup K (fun j => if j % 2 = 0 then 0 else 1) i) (clippedCircuit K tail))

theorem clipped_circuit_range (K : Nat) (digits : List R) :
    0 ≤ clippedCircuit K digits ∧ clippedCircuit K digits ≤ 1 := by
  cases digits with
  | nil => simp only [clippedCircuit]; constructor <;> grind
  | cons i tail => exact clip_range 1 _ (by grind)

theorem clipped_circuit_exact (K : Nat) (hK : 0 < K) (digits : List Nat)
    (valid : ∀ i, i ∈ digits → i < K) :
    clippedCircuit K (digits.map (fun i : Nat => (i:R))) =
      (snakeRank K digits:R)/((K^digits.length:Nat):R) := by
  induction digits with
  | nil => simp [clippedCircuit, snakeRank, Semiring.natCast_zero,
      Field.div_eq_mul_inv, Semiring.zero_mul]
  | cons i tail ih =>
    have hi := valid i (by simp)
    have ht : ∀ j, j ∈ tail → j < K := by
      intro j hj
      exact valid j (by simp [hj])
    simp only [List.map_cons, clippedCircuit, List.length_map]
    rw [lookup_at_index K i hi, ih ht,
      normalized_step_exact K (K^tail.length) i (snakeRank K tail) hK (snake_rank_bound K hK tail ht)]
    have hstep := normalized_rank_range (R := R) K hK (i::tail) valid
    simp only [snakeRank, List.length_cons, Nat.pow_succ'] at hstep ⊢
    exact clip_identity 1 _ hstep

def symmetricClip (C x : R) : R := clip (2*C) (x+C) - C

theorem symmetric_clip_range (C x : R) (hC : 0 ≤ C) :
    -C ≤ symmetricClip C x ∧ symmetricClip C x ≤ C := by
  have h := clip_range (2*C) (x+C) (by grind)
  unfold symmetricClip
  constructor <;> grind

theorem symmetric_clip_identity (C x : R) (hx : -C ≤ x ∧ x ≤ C) :
    symmetricClip C x = x := by
  unfold symmetricClip
  rw [clip_identity _ _ (by constructor <;> grind)]
  grind

def captureStream (C target : R) (values : Nat → R) : Nat → R
  | 0 => 0
  | n+1 => symmetricClip C (captureStream C target values n +
      gate C (triangle (n:R) target) (values n))

/-- Off the safe set, capture registers remain bounded after every update. -/
theorem capture_stream_range (n : Nat) (C target : R) (hC : 0 ≤ C) (values : Nat → R) :
    -C ≤ captureStream C target values n ∧ captureStream C target values n ≤ C := by
  cases n with
  | zero => simp only [captureStream]; constructor <;> grind
  | succ n => exact symmetric_clip_range C _ hC

/-- On rank nodes all clips preserve the exact one-hot capture. -/
theorem capture_stream_at_index (n t : Nat) (C : R) (hC : 0 ≤ C) (values : Nat → R)
    (bounds : ∀ j, j < n → -C ≤ values j ∧ values j ≤ C) :
    captureStream C (t:R) values n = if t < n then values t else 0 := by
  induction n with
  | zero => simp [captureStream]
  | succ n ih =>
    rw [captureStream, ih (fun j hj => bounds j (by omega)), triangle_index]
    by_cases h : n = t
    · subst t
      rw [if_neg (Nat.lt_irrefl n), if_pos rfl,
        gate_one C (values n) (bounds n (by omega)), AddCommMonoid.zero_add,
        symmetric_clip_identity C (values n) (bounds n (by omega)), if_pos (by omega)]
    · rw [if_neg h, gate_zero, AddCommMonoid.add_zero]
      by_cases ht : t < n
      · rw [if_pos ht, if_pos (by omega), symmetric_clip_identity C (values t) (bounds t (by omega))]
      · rw [if_neg ht, if_neg (by omega), symmetric_clip_identity C 0 (by constructor <;> grind)]

theorem capture_stream_vector (n t J : Nat) (ht : t < n) (C : R) (hC : 0 ≤ C)
    (jets : Nat → Fin J → R)
    (bounds : ∀ j, j < n → ∀ beta, -C ≤ jets j beta ∧ jets j beta ≤ C) :
    (fun beta => captureStream C (t:R) (fun j => jets j beta) n) = jets t := by
  funext beta
  rw [capture_stream_at_index n t C hC _ (fun j hj => bounds j hj beta), if_pos ht]

/-- Full safe spatial extraction with bounded recurrent capture registers. -/
theorem safe_spatial_stream (n K J : Nat) (hK : 0 < K) (delta : R) (hd : 0 < delta)
    (sites : List (Site R)) (valid : validSites n K delta sites) (C : R) (hC : 0 ≤ C)
    (jets : Nat → Fin J → R)
    (bounds : ∀ j, j < K^sites.length → ∀ beta, -C ≤ jets j beta ∧ jets j beta ≤ C) :
    (fun beta => captureStream C
      (((K^sites.length:Nat):R) * clippedCircuit K (decodedDigits n K delta sites))
      (fun j => jets j beta) (K^sites.length)) = jets (snakeRank K (sites.map Site.fine)) := by
  have hvalid : ∀ i, i ∈ sites.map Site.fine → i < K := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨s, hs, he⟩
    subst i
    exact (valid s hs).2.1
  rw [decoded_digits_exact n K delta hd sites valid]
  have heq : sites.map (fun s => (s.fine:R)) =
      (sites.map Site.fine).map (fun i : Nat => (i:R)) := by simp [List.map_map]
  rw [heq, clipped_circuit_exact K hK _ hvalid]
  simp only [List.length_map]
  have hBn : ((K^sites.length:Nat):R) ≠ 0 := by
    have := OrderedRing.pos_natCast_of_pos (R := R) (K^sites.length) (Nat.pow_pos hK)
    grind
  rw [CommSemiring.mul_comm ((K^sites.length:Nat):R), Field.div_mul_cancel hBn]
  apply capture_stream_vector
  · simpa only [List.length_map] using snake_rank_bound K hK (sites.map Site.fine) hvalid
  · exact hC
  · exact bounds

end MathCan.SpatialClipped

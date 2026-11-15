import MathCan.SpatialScalar

/-!
Finite spatial routing after the safe-cell ramp interface: exact table lookup,
serpentine rank, and vector jet capture. All operations are explicit scalar
formulas. Circuit compilation and analytic error estimates are separate.
-/
namespace MathCan.SpatialRouting
open Std Lean.Grind MathCan.SpatialScalar
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast

def lookup (n : Nat) (values : Nat → R) (z : R) : R :=
  sum n (fun j => values j * triangle z (j:R))

/-- The triangular table reads exactly its stored value at every address node. -/
theorem lookup_at_index (n t : Nat) (ht : t < n) (values : Nat → R) :
    lookup n values (t:R) = values t := by
  unfold lookup
  calc
    _ = sum n (fun j => if j = t then values t else 0) := by
      apply sum_congr
      intro j hj
      rw [triangle_index]
      by_cases h : j = t
      · subst j
        simp [Semiring.mul_one]
      · simp [h, Ne.symm h, Semiring.mul_zero]
    _ = values t := sum_single n t ht (values t)

/-- A triangular basis function is a three-hinge affine ReLU formula. -/
theorem triangle_hinges (z t : R) :
    triangle z t = relu (z-t+1) - 2*relu (z-t) + relu (z-t-1) := by
  unfold triangle relu
  repeat' split <;> grind

def snakeRank (K : Nat) : List Nat → Nat
  | [] => 0
  | i :: tail =>
    let B := K^tail.length
    let r := snakeRank K tail
    if i % 2 = 0 then i*B+r else i*B+(B-1-r)

/-- Both orientations of the snake stay within the block. -/
theorem snake_rank_bound (K : Nat) (hK : 0 < K) (digits : List Nat)
    (valid : ∀ i, i ∈ digits → i < K) : snakeRank K digits < K^digits.length := by
  induction digits with
  | nil => simp [snakeRank]
  | cons i tail ih =>
    have hi := valid i (by simp)
    have ht : ∀ j, j ∈ tail → j < K := by
      intro j hj
      exact valid j (by simp [hj])
    have hr := ih ht
    have hb : 0 < K^tail.length := Nat.pow_pos hK
    have hm := Nat.mul_le_mul_right (K^tail.length) (show i+1 ≤ K by omega)
    simp only [Nat.add_mul, Nat.one_mul] at hm
    simp only [snakeRank, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (K^tail.length) K]
    split <;> omega

def snakeStep (B : Nat) (i b r : R) : R :=
  i*(B:R) + r + gate (2*(B:R)) b ((B:R)-1-2*r)

/-- The bounded binary gate implements reversal of a rank inside B sites. -/
theorem snake_step_exact (B i r : Nat) (hr : r < B) :
    snakeStep B (i:R) (if i % 2 = 0 then 0 else 1) (r:R) =
      ((if i % 2 = 0 then i*B+r else i*B+(B-1-r):Nat):R) := by
  have hr0 : 0 ≤ (r:R) := OrderedRing.natCast_nonneg
  have hb0 : 0 ≤ (B:R) := OrderedRing.natCast_nonneg
  have hle := OrderedRing.natCast_le_natCast_of_le (R := R) (r+1) B (by omega)
  simp only [Semiring.natCast_succ] at hle
  have hsum : r+(B-1-r)+1 = B := by omega
  have hs := congrArg (fun n : Nat => (n:R)) hsum
  simp only [Semiring.natCast_add, Semiring.natCast_one] at hs
  unfold snakeStep
  by_cases h : i % 2 = 0
  · rw [if_pos h, if_pos h, gate_zero]
    simp only [Semiring.natCast_add, Semiring.natCast_mul]
    grind
  · rw [if_neg h, if_neg h, gate_one _ _ (by constructor <;> grind)]
    simp only [Semiring.natCast_add, Semiring.natCast_mul]
    grind

def snakeCircuit (K : Nat) : List Nat → R
  | [] => 0
  | i :: tail => snakeStep (K^tail.length) (i:R)
      (if i % 2 = 0 then 0 else 1) (snakeCircuit K tail)

/-- The scalar gate recurrence computes the exact integer serpentine address. -/
theorem snake_circuit_exact (K : Nat) (hK : 0 < K) (digits : List Nat)
    (valid : ∀ i, i ∈ digits → i < K) :
    snakeCircuit (R := R) K digits = (snakeRank K digits:R) := by
  induction digits with
  | nil => simp only [snakeCircuit, snakeRank, Semiring.natCast_zero]
  | cons i tail ih =>
    have ht : ∀ j, j ∈ tail → j < K := by
      intro j hj
      exact valid j (by simp [hj])
    simp only [snakeCircuit, snakeRank]
    rw [ih ht, snake_step_exact _ _ _ (snake_rank_bound K hK tail ht)]

/-- Composition of the rank circuit and streamed vector capture. -/
theorem routing_capture (K J : Nat) (hK : 0 < K) (digits : List Nat)
    (valid : ∀ i, i ∈ digits → i < K) (C : R) (jets : Nat → Fin J → R)
    (bounds : ∀ j, j < K^digits.length → ∀ beta, -C ≤ jets j beta ∧ jets j beta ≤ C) :
    (fun beta => sum (K^digits.length) (fun j =>
      gate C (triangle (j:R) (snakeCircuit K digits)) (jets j beta))) =
      jets (snakeRank K digits) := by
  rw [snake_circuit_exact K hK digits valid]
  exact capture_vector _ _ J (snake_rank_bound K hK digits valid) C jets bounds

end MathCan.SpatialRouting

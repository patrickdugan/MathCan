import Init
import Init.Grind.Ordered.Field

/-!
The ordered-scalar spatial interface. These theorems use only the standard
ordered-field laws from Lean core. No approximation or circuit-correctness
claim is assumed. `safeCell` is a pair of explicit geometric inequalities.
Coordinates are measured in fine-cell units: u = m*x + 1 - theta.
-/
namespace MathCan.SpatialScalar
open Std Lean.Grind
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast

def relu (x : R) : R := if x < 0 then 0 else x
def clip (cap x : R) : R := relu x - relu (x - cap)
def gate (C b z : R) : R := relu (z + C*b) - relu (z - C*b) - C*b
def ramp (delta x : R) : R := (relu (x + delta) - relu (x - delta)) / (2*delta)

theorem relu_nonneg (x : R) : 0 ≤ relu x := by
  unfold relu
  split <;> grind

theorem relu_of_nonneg (x : R) (h : 0 ≤ x) : relu x = x := by
  unfold relu
  split <;> grind

theorem relu_of_nonpos (x : R) (h : x ≤ 0) : relu x = 0 := by
  unfold relu
  split <;> grind

theorem clip_range (cap x : R) (hc : 0 ≤ cap) :
    0 ≤ clip cap x ∧ clip cap x ≤ cap := by
  unfold clip relu
  repeat' split <;> grind

theorem clip_identity (cap x : R) (hx : 0 ≤ x ∧ x ≤ cap) : clip cap x = x := by
  unfold clip
  rw [relu_of_nonneg _ hx.1, relu_of_nonpos _ (by grind)]
  grind

theorem clip_step (cap x step : R) (hc : 0 ≤ cap) (hs : 0 ≤ step) :
    0 ≤ clip cap (x+step) - clip cap x ∧
    clip cap (x+step) - clip cap x ≤ step := by
  unfold clip relu
  repeat' split <;> grind

theorem gate_zero (C z : R) : gate C 0 z = 0 := by
  simp only [gate, Semiring.mul_zero]
  grind

theorem gate_one (C z : R) (hz : -C ≤ z ∧ z ≤ C) : gate C 1 z = z := by
  unfold gate
  rw [Semiring.mul_one, relu_of_nonneg _ (by grind), relu_of_nonpos _ (by grind)]
  grind

theorem gate_binary (C b z : R) (hb : b = 0 ∨ b = 1) (hz : -C ≤ z ∧ z ≤ C) :
    gate C b z = b*z := by
  rcases hb with h | h
  · rw [h, gate_zero, Semiring.zero_mul]
  · rw [h, gate_one C z hz, Semiring.one_mul]

theorem ramp_low (delta x : R) (hd : 0 < delta) (hx : x ≤ -delta) :
    ramp delta x = 0 := by
  unfold ramp
  rw [relu_of_nonpos _ (by grind), relu_of_nonpos _ (by grind)]
  rw [AddCommGroup.sub_self, Field.div_eq_mul_inv, Semiring.zero_mul]

theorem ramp_high (delta x : R) (hd : 0 < delta) (hx : delta ≤ x) :
    ramp delta x = 1 := by
  unfold ramp
  rw [relu_of_nonneg _ (by grind), relu_of_nonneg _ (by grind)]
  have hn : x+delta-(x-delta) = 2*delta := by grind
  rw [hn, Field.div_eq_mul_inv, Field.mul_inv_cancel (by grind)]

/-- Finite summation with every addition explicit; no external finite-set library. -/
def sum (n : Nat) (f : Nat → R) : R :=
  match n with
  | 0 => 0
  | n+1 => sum n f + f n

theorem sum_congr (n : Nat) (f g : Nat → R) (h : ∀ j, j < n → f j = g j) :
    sum n f = sum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum]
    rw [ih (by intros; apply h; omega), h n (by omega)]

theorem sum_prefix (n c : Nat) (hc : c ≤ n) :
    sum n (fun j => if j < c then (1:R) else 0) = (c:R) := by
  induction n generalizing c with
  | zero =>
    have he : c = 0 := by omega
    subst c
    simp only [sum, Semiring.natCast_zero]
  | succ n ih =>
    by_cases h : c ≤ n
    · rw [sum, ih c h, if_neg (by omega), AddCommMonoid.add_zero]
    · have he : c = n+1 := by omega
      subst c
      have hh := ih (c := n) (Nat.le_refl n)
      have heq : sum n (fun j => if j < n+1 then (1:R) else 0) =
          sum n (fun j => if j < n then (1:R) else 0) := by
        apply sum_congr
        intro j hj
        simp [hj, show j < n+1 by omega]
      rw [sum, if_pos (Nat.lt_succ_self n), heq, hh, Semiring.natCast_succ]

def safeCell (delta u : R) (cell : Nat) : Prop :=
  (cell:R) + delta ≤ u ∧ u ≤ (cell:R) + 1 - delta

/-- A safe cell gives exactly its index as a sum of ReLU step plateaus. -/
theorem fine_address (n cell : Nat) (hc : cell ≤ n) (delta u : R)
    (hd : 0 < delta) (hu : safeCell delta u cell) :
    sum n (fun j => ramp delta (u - ((j+1:Nat):R))) = (cell:R) := by
  rw [← sum_prefix n cell hc]
  apply sum_congr
  intro j hj
  by_cases h : j < cell
  · rw [if_pos h]
    apply ramp_high _ _ hd
    have hh := OrderedRing.natCast_le_natCast_of_le (R := R) (j+1) cell (by omega)
    unfold safeCell at hu
    grind
  · rw [if_neg h]
    apply ramp_low _ _ hd
    have hh := OrderedRing.natCast_le_natCast_of_le (R := R) (cell+1) (j+1) (by omega)
    simp only [Semiring.natCast_succ] at hh
    unfold safeCell at hu
    grind

def coarseAddress (n K : Nat) (delta u : R) : R :=
  sum n (fun j => ramp delta (u - (((j+1)*K:Nat):R)))

def fineAddress (K : Nat) (delta v : R) : R :=
  sum (K-1) (fun j => ramp delta (v - ((j+1:Nat):R)))

/-- All coarse ramps are on plateaus when the fine cell is safe. -/
theorem coarse_address (n K c i : Nat) (hc : c ≤ n) (hi : i < K)
    (delta u : R) (hd : 0 < delta) (hu : safeCell delta u (c*K+i)) :
    coarseAddress n K delta u = (c:R) := by
  unfold coarseAddress
  rw [← sum_prefix n c hc]
  apply sum_congr
  intro j hj
  by_cases h : j < c
  · rw [if_pos h]
    apply ramp_high _ _ hd
    have hn : (j+1)*K ≤ c*K+i := by
      have := Nat.mul_le_mul_right K (show j+1 ≤ c by omega)
      omega
    have hh := OrderedRing.natCast_le_natCast_of_le (R := R) _ _ hn
    unfold safeCell at hu
    grind
  · rw [if_neg h]
    apply ramp_low _ _ hd
    have hn : c*K+i+1 ≤ (j+1)*K := by
      have hh := Nat.mul_le_mul_right K (show c+1 ≤ j+1 by omega)
      simp only [Nat.add_mul, Nat.one_mul] at hh ⊢
      omega
    have hh := OrderedRing.natCast_le_natCast_of_le (R := R) _ _ hn
    simp only [Semiring.natCast_succ] at hh
    unfold safeCell at hu
    grind

/-- Exact coarse-to-fine composition, including the padded edge block c=n. -/
theorem spatial_address (n K c i : Nat) (hc : c ≤ n) (hi : i < K)
    (delta u : R) (hd : 0 < delta) (hu : safeCell delta u (c*K+i)) :
    coarseAddress n K delta u = (c:R) ∧
    fineAddress K delta (u - coarseAddress n K delta u * (K:R)) = (i:R) := by
  have hcoarse := coarse_address n K c i hc hi delta u hd hu
  refine ⟨hcoarse, ?_⟩
  rw [hcoarse]
  apply fine_address (K-1) i (by omega) delta _ hd
  unfold safeCell at hu ⊢
  simp only [Semiring.natCast_add, Semiring.natCast_mul] at hu
  constructor <;> grind

/-- Clipping a boundary anchor into the domain preserves a unit local coordinate. -/
theorem boundary_anchor (cap p theta delta : R) (cell : Nat)
    (hp : 0 ≤ p ∧ p ≤ cap) (hd : 0 < delta)
    (hu : safeCell delta (p+1-theta) cell) :
    0 ≤ p - clip cap ((cell:R)+theta-1) ∧
    p - clip cap ((cell:R)+theta-1) ≤ 1 := by
  unfold safeCell at hu
  unfold clip relu
  repeat' split <;> grind

theorem local_coordinate_exact (cap p theta delta : R) (cell : Nat)
    (hp : 0 ≤ p ∧ p ≤ cap) (hd : 0 < delta)
    (hu : safeCell delta (p+1-theta) cell) :
    clip 1 (p - clip cap ((cell:R)+theta-1)) =
      p - clip cap ((cell:R)+theta-1) := by
  exact clip_identity _ _ (boundary_anchor cap p theta delta cell hp hd hu)

def triangle (u t : R) : R := relu (1 - relu (u-t) - relu (t-u))

/-- The ReLU triangular selector is exactly one-hot at integral rank nodes. -/
theorem triangle_index (i t : Nat) :
    triangle (i:R) (t:R) = if i = t then 1 else 0 := by
  by_cases h : i = t
  · subst i
    unfold triangle relu
    repeat' split <;> grind
  · rw [if_neg h]
    have hh : i+1 ≤ t ∨ t+1 ≤ i := by omega
    rcases hh with hh | hh
    · have he := OrderedRing.natCast_le_natCast_of_le (R := R) _ _ hh
      simp only [Semiring.natCast_succ] at he
      unfold triangle relu
      repeat' split <;> grind
    · have he := OrderedRing.natCast_le_natCast_of_le (R := R) _ _ hh
      simp only [Semiring.natCast_succ] at he
      unfold triangle relu
      repeat' split <;> grind

theorem sum_zero (n : Nat) : sum n (fun _ => (0:R)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum, ih, AddCommMonoid.add_zero]

theorem sum_single (n t : Nat) (ht : t < n) (v : R) :
    sum n (fun j => if j = t then v else 0) = v := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    by_cases h : t = n
    · subst t
      have hz : sum n (fun j => if j = n then v else 0) = 0 := by
        calc
          _ = sum n (fun _ => (0:R)) := by
            apply sum_congr
            intro j hj
            simp [show j ≠ n by omega]
          _ = 0 := sum_zero n
      rw [sum, if_pos rfl, hz, AddCommMonoid.zero_add]
    · rw [sum, if_neg (Ne.symm h), ih t (by omega), AddCommMonoid.add_zero]

/-- Every streamed jet contributes zero except the selected jet, which is exact. -/
theorem capture_sum (n t : Nat) (ht : t < n) (C : R) (values : Nat → R)
    (bounds : ∀ j, j < n → -C ≤ values j ∧ values j ≤ C) :
    sum n (fun j => gate C (triangle (j:R) (t:R)) (values j)) = values t := by
  rw [← sum_single n t ht (values t)]
  apply sum_congr
  intro j hj
  rw [triangle_index]
  by_cases h : j = t
  · rw [if_pos h, gate_one C (values j) (bounds j hj)]
    simp [h]
  · rw [if_neg h, gate_zero]
    simp [h]

/-- Jet coordinates can be captured simultaneously with the same scalar selector. -/
theorem capture_vector (n t J : Nat) (ht : t < n) (C : R) (jets : Nat → Fin J → R)
    (bounds : ∀ j, j < n → ∀ beta, -C ≤ jets j beta ∧ jets j beta ≤ C) :
    (fun beta => sum n (fun j => gate C (triangle (j:R) (t:R)) (jets j beta))) = jets t := by
  funext beta
  exact capture_sum n t ht C (fun j => jets j beta) (fun j hj => bounds j hj beta)

end MathCan.SpatialScalar

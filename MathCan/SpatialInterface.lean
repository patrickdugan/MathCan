import Init

/-!
Exact scaled-integer lemmas for the quantized spatial circuit. Clipped grid
anchors never leave the cube and have bounded integral microsteps. The binary
gate and integer triangular selector give exact one-hot bounded-jet capture.
These statements do not identify a finite test with a real-domain theorem.
-/
namespace MathCan.SpatialInterface

def relu (z : Int) : Int := if z < 0 then 0 else z
def clamp (cap x : Int) : Int :=
  if x < 0 then 0 else if cap < x then cap else x

theorem clamp_range (cap x : Int) (hcap : 0 ≤ cap) :
    0 ≤ clamp cap x ∧ clamp cap x ≤ cap := by
  unfold clamp
  repeat' split <;> omega

/-- Clipping preserves a nonnegative step and can only shorten it. -/
theorem clamp_step (cap x D : Int) (hcap : 0 ≤ cap) (hD : 0 ≤ D) :
    0 ≤ clamp cap (x + D) - clamp cap x ∧
    clamp cap (x + D) - clamp cap x ≤ D := by
  unfold clamp
  repeat' split <;> omega

def anchor (cap D t r : Int) : Int := clamp cap (D * r + t - D)

/-- Translated and clipped grid anchors have integer microsteps in [0,D]. -/
theorem anchor_step (cap D t r : Int) (hcap : 0 ≤ cap) (hD : 0 ≤ D) :
    0 ≤ anchor cap D t (r + 1) - anchor cap D t r ∧
    anchor cap D t (r + 1) - anchor cap D t r ≤ D := by
  have h : D * (r + 1) + t - D = (D * r + t - D) + D := by
    simp only [Int.mul_add, Int.mul_one]
    omega
  unfold anchor
  rw [h]
  exact clamp_step cap _ D hcap hD

def gate (C b z : Int) : Int :=
  relu (z + C * b) - relu (z - C * b) - C * b

theorem gate_zero (C z : Int) : gate C 0 z = 0 := by
  simp [gate]

theorem gate_one (C z : Int) (hC : 0 ≤ C) (hz : -C ≤ z ∧ z ≤ C) :
    gate C 1 z = z := by
  simp only [gate, Int.mul_one]
  unfold relu
  repeat' split <;> omega

def triangle (u t : Int) : Int :=
  relu (1 - relu (u - t) - relu (t - u))

theorem triangle_self (t : Int) : triangle t t = 1 := by
  simp [triangle, relu]

/-- Integer separation makes the triangular ReLU exactly zero off target. -/
theorem triangle_other (u t : Int) (h : u ≠ t) : triangle u t = 0 := by
  unfold triangle relu
  repeat' split <;> omega

/-- Each site adds precisely its jet at the selected index and zero elsewhere. -/
theorem capture_at_index {n : Nat} (C : Int) (hC : 0 ≤ C)
    (values : Fin n → Int) (bounds : ∀ i, -C ≤ values i ∧ values i ≤ C)
    (target i : Fin n) :
    gate C (triangle (Int.ofNat i.val) (Int.ofNat target.val)) (values i) =
      if i = target then values i else 0 := by
  by_cases h : i = target
  · subst i
    rw [triangle_self, gate_one C (values target) hC (bounds target)]
    simp
  · have hval : Int.ofNat i.val ≠ Int.ofNat target.val := by
      intro he
      have hv : i.val = target.val := Int.ofNat.inj he
      exact h (Fin.ext hv)
    rw [triangle_other _ _ hval, gate_zero]
    simp [h]

#check clamp_range
#check clamp_step
#check anchor_step
#check gate_zero
#check gate_one
#check triangle_self
#check triangle_other
#check capture_at_index
#print axioms clamp_range
#print axioms clamp_step
#print axioms anchor_step
#print axioms gate_zero
#print axioms gate_one
#print axioms triangle_self
#print axioms triangle_other
#print axioms capture_at_index

end MathCan.SpatialInterface

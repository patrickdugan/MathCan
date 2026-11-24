import RankSpectral

/-! VPVNP-02C: the actual binary Walsh basis on finite coordinate sets. -/

open scoped BigOperators
open Finset

namespace VPVNP.Binary

abbrev Bits (I : Type*) := I → ZMod 2

theorem bit_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> decide

theorem bit_double (x : ZMod 2) : x+x = 0 := by
  rcases bit_cases x with rfl | rfl <;> decide

theorem bit_sum_zero (x y : ZMod 2) (h : x+y=0) : x=y := by
  exact (add_left_cancel (h.trans (bit_double x).symm)).symm

noncomputable def bitSign (x : ZMod 2) : ℝ := if x=0 then 1 else -1

theorem bitSign_add (x y : ZMod 2) :
    bitSign (x+y) = bitSign x * bitSign y := by
  rcases bit_cases x with rfl | rfl <;>
    rcases bit_cases y with rfl | rfl <;>
    norm_num [bitSign, bit_double]

section Walsh

variable {I : Type*} [Fintype I] [DecidableEq I]

def parityPair (b a : Bits I) : ZMod 2 := ∑ i, b i * a i

def unitBit (i : I) : Bits I := fun j => if j=i then 1 else 0

theorem pairing_add_left (b c a : Bits I) :
    parityPair (b+c) a = parityPair b a + parityPair c a := by
  simp only [parityPair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairing_add_right (b a w : Bits I) :
    parityPair b (a+w) = parityPair b a + parityPair b w := by
  simp only [parityPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairing_symm (b a : Bits I) : parityPair b a = parityPair a b := by
  unfold parityPair
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem pairing_unit (b : Bits I) (i : I) :
    parityPair b (unitBit i) = b i := by
  classical
  unfold parityPair
  rw [Finset.sum_eq_single i]
  · simp [unitBit]
  · intro j hj hji
    simp [unitBit, hji]
  · simp

noncomputable def walsh (b a : Bits I) : ℝ := bitSign (parityPair b a)

theorem walsh_add_left (b c a : Bits I) :
    walsh (b+c) a = walsh b a * walsh c a := by
  simp only [walsh, pairing_add_left, bitSign_add]

theorem walsh_add_right (b a w : Bits I) :
    walsh b (a+w) = walsh b a * walsh b w := by
  simp only [walsh, pairing_add_right, bitSign_add]

theorem walsh_symm (b a : Bits I) : walsh b a = walsh a b := by
  unfold walsh
  rw [pairing_symm b a]

theorem walsh_sign (b a : Bits I) :
    walsh b a = 1 ∨ walsh b a = -1 := by
  unfold walsh bitSign
  split <;> simp

theorem walsh_sum_zero (b : Bits I) (hb : b ≠ 0) :
    (∑ a : Bits I, walsh b a) = 0 := by
  classical
  have hi : ∃ i, b i ≠ 0 := by
    by_contra! h
    apply hb
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hi
  have hsign : walsh b (unitBit i) = -1 := by
    simp [walsh, pairing_unit, bitSign, hi]
  have hshift : (∑ a : Bits I, walsh b (a+unitBit i)) =
      ∑ a : Bits I, walsh b a :=
    (Equiv.addRight (unitBit i)).sum_comp (walsh b)
  simp_rw [walsh_add_right, hsign, mul_neg, mul_one, Finset.sum_neg_distrib] at hshift
  linarith

theorem walsh_sum_at_zero :
    (∑ a : Bits I, walsh 0 a) = (Fintype.card (Bits I) : ℝ) := by
  simp [walsh, parityPair, bitSign]

/-- Full orthogonality for the actual characters, with no spectral hypotheses. -/
theorem walsh_orthogonal (b c : Bits I) :
    (∑ a : Bits I, walsh b a * walsh c a) =
      if b=c then (Fintype.card (Bits I) : ℝ) else 0 := by
  classical
  calc
    (∑ a : Bits I, walsh b a * walsh c a) =
        ∑ a : Bits I, walsh (b+c) a := by
      simp_rw [walsh_add_left]
    _ = _ := by
      by_cases h : b=c
      · subst c
        have hz : b+b=0 := by
          funext i
          exact bit_double (b i)
        rw [hz, if_pos rfl]
        exact walsh_sum_at_zero
      · have hz : b+c ≠ 0 := by
          intro hz
          apply h
          funext i
          have hi := congrFun hz i
          change b i+c i=0 at hi
          exact bit_sum_zero _ _ hi
        rw [if_neg h]
        exact walsh_sum_zero _ hz

theorem walsh_dual_orthogonal (x a : Bits I) :
    (∑ b : Bits I, walsh b x * walsh b a) =
      if x=a then (Fintype.card (Bits I) : ℝ) else 0 := by
  calc
    (∑ b : Bits I, walsh b x * walsh b a) =
        ∑ b : Bits I, walsh x b * walsh a b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [walsh_symm b x, walsh_symm b a]
    _ = _ := walsh_orthogonal x a

noncomputable def walshCoeff (f : Bits I → ℝ) (b : Bits I) : ℝ :=
    (∑ x : Bits I, f x * walsh b x) / (Fintype.card (Bits I) : ℝ)

theorem walsh_reconstruct_raw (f : Bits I → ℝ) (a : Bits I) :
    (∑ b : Bits I, (∑ x : Bits I, f x * walsh b x) * walsh b a) =
      f a * (Fintype.card (Bits I) : ℝ) := by
  classical
  calc
    (∑ b : Bits I, (∑ x : Bits I, f x * walsh b x) * walsh b a) =
        ∑ b : Bits I, ∑ x : Bits I, f x * (walsh b x * walsh b a) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ x : Bits I, f x * (∑ b : Bits I, walsh b x * walsh b a) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = ∑ x : Bits I, f x * (if x=a then (Fintype.card (Bits I) : ℝ) else 0) := by
      simp_rw [walsh_dual_orthogonal]
    _ = _ := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro x hx hne
        simp [hne]
      · simp

/-- Inversion for every real-valued binary-coordinate observer. -/
theorem walsh_reconstruct (f : Bits I → ℝ) (a : Bits I) :
    f a = ∑ b : Bits I, walshCoeff f b * walsh b a := by
  classical
  have hnat : 0 < Fintype.card (Bits I) := Fintype.card_pos
  have hn : (Fintype.card (Bits I) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnat)
  calc
    f a = (f a * (Fintype.card (Bits I) : ℝ)) /
        (Fintype.card (Bits I) : ℝ) := (eq_div_iff hn).2 rfl
    _ = (∑ b : Bits I, (∑ x : Bits I, f x * walsh b x) * walsh b a) /
        (Fintype.card (Bits I) : ℝ) := by rw [walsh_reconstruct_raw]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b hb
      unfold walshCoeff
      ring

/-- The previous conditional shift identity is now specialized to actual Walsh characters. -/
theorem actual_shift_energy (f : Bits I → ℝ) (w : Bits I) :
    (∑ a : Bits I, (f (a+w)-f a)^2) =
      (Fintype.card (Bits I) : ℝ) *
        ∑ b : Bits I, (walshCoeff f b * (walsh b w-1))^2 := by
  exact VPVNP.shift_energy walsh f (walshCoeff f)
    walsh_orthogonal walsh_add_right (walsh_reconstruct f) w

/-- Coordinatewise vector shift energy for arbitrary finite output dimension. -/
theorem actual_vector_shift_energy {J : Type*} [Fintype J]
    (f : Bits I → J → ℝ) (w : Bits I) :
    (∑ a : Bits I, ∑ j : J, (f (a+w) j-f a j)^2) =
      ∑ j : J, (Fintype.card (Bits I) : ℝ) *
        ∑ b : Bits I, (walshCoeff (fun a => f a j) b * (walsh b w-1))^2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact actual_shift_energy (fun a => f a j) w

/-- Unnormalized energy for an arbitrary finite increment set. -/
theorem increment_energy (f : Bits I → ℝ) (S : Finset (Bits I)) :
    (∑ w ∈ S, ∑ a : Bits I, (f (a+w)-f a)^2) =
      (Fintype.card (Bits I) : ℝ) *
        ∑ b : Bits I, (walshCoeff f b)^2 * ∑ w ∈ S, (walsh b w-1)^2 := by
  calc
    (∑ w ∈ S, ∑ a : Bits I, (f (a+w)-f a)^2) =
        ∑ w ∈ S, (Fintype.card (Bits I) : ℝ) *
          ∑ b : Bits I, (walshCoeff f b * (walsh b w-1))^2 := by
      apply Finset.sum_congr rfl
      intro w hw
      exact actual_shift_energy f w
    _ = (Fintype.card (Bits I) : ℝ) *
        ∑ w ∈ S, ∑ b : Bits I, (walshCoeff f b * (walsh b w-1))^2 := by
      rw [Finset.mul_sum]
    _ = (Fintype.card (Bits I) : ℝ) *
        ∑ b : Bits I, ∑ w ∈ S, (walshCoeff f b * (walsh b w-1))^2 := by
      congr 1
      exact Finset.sum_comm
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring

end Walsh

/-- The closed form is the unique solution of the elementary character recurrence.
This algebraic lemma does not assume the matrix distribution satisfies it. -/
theorem recurrence_unique (F G : ℕ → ℕ → ℝ)
    (Fzero : ∀ n, F n 0 = 1) (Gzero : ∀ n, G n 0 = 1)
    (Fstep : ∀ n k, F (n+1) (k+1) = -F n k / ((2:ℝ)^(n+1)-1))
    (Gstep : ∀ n k, G (n+1) (k+1) = -G n k / ((2:ℝ)^(n+1)-1)) :
    ∀ n k, k ≤ n → F n k = G n k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have h : k=0 := by omega
    subst k
    rw [Fzero, Gzero]
  | succ n ih =>
    intro k hk
    cases k with
    | zero => rw [Fzero, Gzero]
    | succ k =>
      rw [Fstep, Gstep, ih k (by omega)]

end VPVNP.Binary

#print axioms VPVNP.Binary.pairing_unit
#print axioms VPVNP.Binary.walsh_sum_zero
#print axioms VPVNP.Binary.walsh_orthogonal
#print axioms VPVNP.Binary.walsh_dual_orthogonal
#print axioms VPVNP.Binary.walsh_reconstruct
#print axioms VPVNP.Binary.actual_shift_energy
#print axioms VPVNP.Binary.actual_vector_shift_energy
#print axioms VPVNP.Binary.increment_energy
#print axioms VPVNP.Binary.recurrence_unique

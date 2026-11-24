import Mathlib.NumberTheory.Multiplicity
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate
open Finset

namespace CLN02

/-- For an odd prime, positive principal unit z, and positive n,
the full prime-power return criterion is equivalent to a divisibility
condition on n. This is the precise LTE input to the period bound. -/
theorem odd_prime_return_iff (p z t n : ℕ) [Fact p.Prime]
    (hp : Odd p) (hz : 1 < z) (hprincipal : p ∣ z - 1)
    (hunit : ¬ p ∣ z) (hn : n ≠ 0) :
    p ^ t ∣ z ^ n - 1 ↔ p ^ (t - padicValNat p (z - 1)) ∣ n := by
  have hpow : 1 < z ^ n := by
    simpa using Nat.pow_lt_pow_left hz hn
  have hlte : padicValNat p (z ^ n - 1) =
      padicValNat p (z - 1) + padicValNat p n := by
    simpa only [one_pow] using
      (padicValNat.pow_sub_pow (p := p) (x := z) (y := 1)
        hp hz hprincipal hunit hn)
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  rw [Nat.pow_dvd_iff_le_padicValNat hp1 (Nat.sub_ne_zero_of_lt hpow),
      Nat.pow_dvd_iff_le_padicValNat hp1 hn, hlte]
  omega

/-- The odd-prime order of a principal unit in ZMod(p^t). -/
theorem odd_prime_principal_order (p z t : ℕ) [Fact p.Prime]
    (hp : Odd p) (hz : 1 < z) (hprincipal : p ∣ z - 1)
    (hunit : ¬ p ∣ z) :
    orderOf (z : ZMod (p ^ t)) = p ^ (t - padicValNat p (z - 1)) := by
  let q := p ^ (t - padicValNat p (z - 1))
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos _
  have hreturn (n : ℕ) (hn : n ≠ 0) :
      (z : ZMod (p ^ t)) ^ n = 1 ↔ q ∣ n := by
    have hpow : 1 < z ^ n := by
      simpa using Nat.pow_lt_pow_left hz hn
    have heq : (z : ZMod (p ^ t)) ^ n = 1 ↔
        p ^ t ∣ z ^ n - 1 := by
      rw [← sub_eq_zero]
      rw [← Nat.cast_pow, ← Nat.cast_one,
        ← Nat.cast_sub (Nat.le_of_lt hpow), ZMod.natCast_eq_zero_iff]
    exact heq.trans (odd_prime_return_iff p z t n hp hz hprincipal hunit hn)
  have hqreturn := (hreturn q hq.ne').2 (dvd_refl q)
  have hpos : 0 < orderOf (z : ZMod (p ^ t)) :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨q, hq, hqreturn⟩).orderOf_pos
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hqreturn)
    ((hreturn _ hpos.ne').1 (pow_orderOf_eq_one _))

/-- 2-adic return criterion at the even exponent 2*n.
The exponent offset is v_2(b-1)+v_2(b+1), so no unjustified
odd-prime LTE invocation at p=2 is needed. -/
theorem two_prime_even_return_iff (b t n : ℕ)
    (hb : 1 < b) (hprincipal : 2 ∣ b - 1) (hunit : ¬ 2 ∣ b)
    (hn : n ≠ 0) :
    2 ^ t ∣ b ^ (2 * n) - 1 ↔
      2 ^ (t - (padicValNat 2 (b - 1) + padicValNat 2 (b + 1))) ∣ n := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h2n : 2 * n ≠ 0 := by omega
  have hev : Even (2 * n) := ⟨n, by omega⟩
  have hpow : 1 < b ^ (2 * n) := by
    simpa using Nat.pow_lt_pow_left hb h2n
  have hlte := padicValNat.pow_two_sub_pow (x := b) (y := 1)
    hb hprincipal hunit h2n hev
  simp only [one_pow] at hlte
  have hval : padicValNat 2 (2 * n) = 1 + padicValNat 2 n := by
    rw [padicValNat.mul (by decide : (2 : ℕ) ≠ 0) hn, padicValNat_self]
  rw [hval] at hlte
  rw [Nat.pow_dvd_iff_le_padicValNat (by decide : (2 : ℕ) ≠ 1)
      (Nat.sub_ne_zero_of_lt hpow),
    Nat.pow_dvd_iff_le_padicValNat (by decide : (2 : ℕ) ≠ 1) hn]
  omega

section Fourier

variable {M : ℕ} [NeZero M]

/-- Orthogonality of the actual complex-valued standard additive
character of ZMod M, including the modulus-one case. -/
theorem character_sum (k : ZMod M) :
    (∑ a : ZMod M, ZMod.stdAddChar (k * a)) =
      if k = 0 then (M : ℂ) else 0 := by
  classical
  by_cases hk : k = 0
  · simp [hk, ZMod.card]
  · have hχ : ZMod.stdAddChar.mulShift k ≠ 0 := by
      intro heq
      have h := congrArg (fun f : AddChar (ZMod M) ℂ => f 1) heq
      have h' : ZMod.stdAddChar k = ZMod.stdAddChar (0 : ZMod M) := by
        simpa only [AddChar.mulShift_apply, mul_one, AddChar.zero_apply,
          AddChar.map_zero_eq_one] using h
      exact hk (ZMod.injective_stdAddChar h')
    rw [if_neg hk]
    exact (AddChar.sum_eq_zero_iff_ne_zero).2 hχ

/-- Character cross-Gram matrix is exactly M times the equality kernel. -/
theorem character_cross (r s : ZMod M) :
    (∑ a : ZMod M, ZMod.stdAddChar ((r - s) * a)) =
      if r = s then (M : ℂ) else 0 := by
  simpa only [sub_eq_zero] using character_sum (r - s)

/-- Finite Fourier collision identity for arbitrary complex coefficients
and arbitrary (possibly repeated) frequencies; using a bilinear form
makes the collision structure explicit. -/
theorem collision_bilinear {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → ZMod M) (s : κ → ZMod M) (u : ι → ℂ) (v : κ → ℂ) :
    (∑ a : ZMod M,
      (∑ i, u i * ZMod.stdAddChar (r i * a)) *
      (∑ j, v j * ZMod.stdAddChar (-(s j * a)))) =
    ∑ i, ∑ j, (u i * v j) * (if r i = s j then (M : ℂ) else 0) := by
  classical
  calc
    _ = ∑ a : ZMod M, ∑ i, ∑ j,
        (u i * v j) * ZMod.stdAddChar ((r i - s j) * a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    _ = ∑ i, ∑ j, ∑ a : ZMod M,
        (u i * v j) * ZMod.stdAddChar ((r i - s j) * a) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum, character_cross]

/-- The conjugate of a Fourier phase is the phase of the negative. -/
theorem conj_character (a : ZMod M) :
    conj (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [AddChar.map_neg_eq_inv]
  apply Eq.symm
  apply Complex.inv_eq_conj
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- The Fourier energy identity in the supplied manuscript, before
dividing by N^2 and applying conditional prefix weights. -/
theorem collision_energy {ι : Type*} [Fintype ι]
    (r : ι → ZMod M) (w : ι → ℂ) :
    (∑ a : ZMod M,
      ((∑ i, w i * ZMod.stdAddChar (r i * a)) *
        conj (∑ i, w i * ZMod.stdAddChar (r i * a)))) =
      ∑ i, ∑ j, (w i * conj (w j)) *
        (if r i = r j then (M : ℂ) else 0) := by
  classical
  simp only [map_sum, map_mul, conj_character]
  exact collision_bilinear r r w (fun i => conj (w i))

end Fourier

#print axioms odd_prime_return_iff
#print axioms odd_prime_principal_order
#print axioms two_prime_even_return_iff
#print axioms character_sum
#print axioms character_cross
#print axioms collision_bilinear
#print axioms conj_character
#print axioms collision_energy

end CLN02

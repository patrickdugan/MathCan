import CLN02
import CLN03
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.FieldTheory.Finite.Basic

open scoped BigOperators ComplexConjugate
open Finset

namespace CLN05

/-- Cancellation of a nonzero frequency factor exactly reduces the
modulus by its gcd, with both implications. -/
theorem gcd_cancel_iff (M h x y : ℕ) (hM : 0 < M) :
    h * x ≡ h * y [MOD M] ↔ x ≡ y [MOD M / M.gcd h] := by
  constructor
  · exact Nat.ModEq.cancel_left_div_gcd hM
  · intro H
    let g := M.gcd h
    have hgM : g ∣ M := Nat.gcd_dvd_left _ _
    have hgh : g ∣ h := Nat.gcd_dvd_right _ _
    have H' := H.mul_left' g
    change g * x ≡ g * y [MOD g * (M / g)] at H'
    rw [Nat.mul_div_cancel' hgM] at H'
    obtain ⟨a, ha⟩ := hgh
    rw [ha]
    simpa only [mul_assoc, mul_left_comm a g] using H'.mul_left a

/-- Powers in a finite group collide precisely at equal remainders
modulo the true order, including order one. -/
theorem pow_collision_iff {G : Type*} [Group G] [Finite G]
    (u : G) (n m : ℕ) :
    u ^ n = u ^ m ↔ m % orderOf u = n % orderOf u := by
  have hp := orderOf_pos u
  constructor
  · intro H
    have heq : u ^ (m % orderOf u) = u ^ (n % orderOf u) := by
      rw [pow_mod_orderOf, pow_mod_orderOf, H]
    exact pow_injOn_Iio_orderOf (x := u)
      (Nat.mod_lt m hp) (Nat.mod_lt n hp) heq
  · intro H
    calc
      u ^ n = u ^ (n % orderOf u) := (pow_mod_orderOf u n).symm
      _ = u ^ (m % orderOf u) := by rw [H]
      _ = u ^ m := pow_mod_orderOf u m

/-- The actual modular frequencies h*b^n, not an arbitrary collision
predicate, have the period of the reduced-modulus unit. -/
theorem orbit_collision_iff (M b h n m : ℕ) (hM : 0 < M)
    (hc : Nat.Coprime b (M / M.gcd h))
    [NeZero (M / M.gcd h)] :
    (h : ZMod M) * (b : ZMod M)^n =
      (h : ZMod M) * (b : ZMod M)^m ↔
    m % orderOf (ZMod.unitOfCoprime b hc) =
      n % orderOf (ZMod.unitOfCoprime b hc) := by
  let u := ZMod.unitOfCoprime b hc
  rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul,
    ZMod.natCast_eq_natCast_iff, gcd_cancel_iff M h (b^n) (b^m) hM,
    ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_pow]
  have heq : ((b : ZMod (M / M.gcd h))^n =
      (b : ZMod (M / M.gcd h))^m) ↔ u^n = u^m := by
    constructor
    · intro H
      apply Units.val_injective
      simpa [u] using H
    · intro H
      simpa [u] using congrArg (fun v : (ZMod (M / M.gcd h))ˣ =>
        (v : ZMod (M / M.gcd h))) H
  exact heq.trans (pow_collision_iff u n m)

/-- A single constant controls all prime-power components of D.
The offset at 2 is handled by the even-exponent LTE theorem. -/
theorem principal_composite_divisibility (D z P : ℕ)
    (hD : D ≠ 0) (hz : 1 < z) (hP : P ≠ 0)
    (hprincipal : ∀ p, p.Prime → p ∣ D → p ∣ z - 1)
    (hreturn : D ∣ z ^ P - 1) :
    D ∣ (z - 1) * (z + 1) * P := by
  have hz1 : z - 1 ≠ 0 := by omega
  have hz2 : z + 1 ≠ 0 := by omega
  have hprod : (z - 1) * (z + 1) * P ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero hz1 hz2) hP
  apply (Nat.factorization_le_iff_dvd hD hprod).mp
  intro p
  by_cases hp0 : D.factorization p = 0
  · simp [hp0]
  have hp : p.Prime := by
    by_contra H
    exact hp0 (Nat.factorization_eq_zero_of_not_prime D H)
  have hpD := Nat.dvd_of_factorization_pos hp0
  have hpz1 := hprincipal p hp hpD
  have hpz : ¬p ∣ z := by
    intro H
    have heq : z = (z - 1) + 1 := by omega
    have H' : p ∣ (z - 1) + 1 := heq ▸ H
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hpz1).mp H')
  letI : Fact p.Prime := ⟨hp⟩
  let t := D.factorization p
  have htD : p ^ t ∣ D :=
    (hp.pow_dvd_iff_le_factorization hD).2 (le_refl _)
  have hret := htD.trans hreturn
  have hval : t ≤ padicValNat p (z - 1) + padicValNat p (z + 1) +
      padicValNat p P := by
    rcases hp.eq_two_or_odd' with hp2 | hodd
    · subst p
      have hpow : 1 ≤ z ^ P := by
        have H : 1 < z ^ P := by simpa using Nat.pow_lt_pow_left hz hP
        omega
      have he : 1 ≡ z ^ P [MOD 2 ^ t] := (Nat.modEq_iff_dvd' hpow).2 hret
      have hs : 1 ≡ z ^ (2 * P) [MOD 2 ^ t] := by
        simpa [pow_mul, Nat.mul_comm 2 P] using he.pow 2
      have hd := hs.dvd'
      have hsmall := (CLN02.two_prime_even_return_iff z t P hz hpz1 hpz hP).1 hd
      have H := (Nat.pow_dvd_iff_le_padicValNat (by decide : (2 : ℕ) ≠ 1) hP).1 hsmall
      omega
    · have hsmall := (CLN02.odd_prime_return_iff p z t P hodd hz hpz1 hpz hP).1 hret
      have H := (Nat.pow_dvd_iff_le_padicValNat hp.ne_one hP).1 hsmall
      omega
  rw [Nat.factorization_mul (Nat.mul_ne_zero hz1 hz2) hP,
    Nat.factorization_mul hz1 hz2, Finsupp.add_apply, Finsupp.add_apply]
  change D.factorization p ≤ _ at hval
  simpa only [Nat.factorization_def _ hp] using hval

/-- A fixed principal unit is obtained by raising b to its order
modulo the source base Q; its constant is independent of k. -/
theorem source_power_period_bound (Q b k h : ℕ) (hQ : 1 < Q)
    (hb : 1 < b) (hh : h ≠ 0) (hc : Nat.Coprime b Q)
    (hred : Nat.Coprime b (Q^k / (Q^k).gcd h))
    [NeZero Q] [NeZero (Q^k / (Q^k).gcd h)] :
    Q^k ∣ (h * ((b ^ orderOf (ZMod.unitOfCoprime b hc) - 1) *
      (b ^ orderOf (ZMod.unitOfCoprime b hc) + 1))) *
        orderOf (ZMod.unitOfCoprime b hred) := by
  let M := Q ^ k
  let g := M.gcd h
  let D := M / g
  let L := orderOf (ZMod.unitOfCoprime b hc)
  let P := orderOf (ZMod.unitOfCoprime b hred)
  let z := b ^ L
  change M ∣ (h * ((z-1)*(z+1))) * P
  have hL : 0 < L := orderOf_pos _
  have hP : 0 < P := orderOf_pos _
  have hz : 1 < z := by
    dsimp [z]
    simpa using Nat.pow_lt_pow_left hb hL.ne'
  have hgM : g ∣ M := Nat.gcd_dvd_left _ _
  have hgh : g ∣ h := Nat.gcd_dvd_right _ _
  have hgD : g * D = M := Nat.mul_div_cancel' hgM
  have hDM : D ∣ M := ⟨g, by calc M = g * D := hgD.symm; _ = D * g := Nat.mul_comm _ _⟩
  have hD : D ≠ 0 := NeZero.ne _
  have hLmod : 1 ≡ z [MOD Q] := by
    apply (ZMod.natCast_eq_natCast_iff 1 z Q).1
    have H := congrArg (fun v : (ZMod Q)ˣ => (v : ZMod Q))
      (pow_orderOf_eq_one (ZMod.unitOfCoprime b hc))
    simpa [z, L] using H.symm
  have hPmod : 1 ≡ b ^ P [MOD D] := by
    apply (ZMod.natCast_eq_natCast_iff 1 (b^P) D).1
    have H := congrArg (fun v : (ZMod D)ˣ => (v : ZMod D))
      (pow_orderOf_eq_one (ZMod.unitOfCoprime b hred))
    simpa [P] using H.symm
  have hreturn : D ∣ z ^ P - 1 := by
    have H : 1 ≡ z ^ P [MOD D] := by
      simpa [z, pow_mul, Nat.mul_comm P L] using hPmod.pow L
    exact H.dvd'
  have hprinc : ∀ p, p.Prime → p ∣ D → p ∣ z-1 := by
    intro p hp hpD
    exact (hLmod.of_dvd (hp.dvd_of_dvd_pow (hpD.trans hDM))).dvd'
  have hbound := principal_composite_divisibility D z P hD hz hP.ne'
    hprinc hreturn
  have H : g * D ∣ h * ((z-1)*(z+1)*P) := mul_dvd_mul hgh hbound
  simpa [hgD, mul_assoc] using H

/-- The complex Fourier identity and conditional energy estimate
are now composed in a single theorem with only the arithmetic
period bound as a premise. The frequencies are the actual orbit. -/
theorem orbit_second_moment (M N b h K : ℕ)
    [NeZero M] [NeZero (M / M.gcd h)]
    (hM : 0 < M) (hN : 0 < N) (hMN : M ≤ N)
    (hc : Nat.Coprime b (M / M.gcd h))
    (hMP : M ≤ K * orderOf (ZMod.unitOfCoprime b hc))
    (w : Fin N → ℂ) (hw : ∀ i, ‖w i‖ = 1)
    (mass : ZMod M → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hmass : ∀ a, mass a ≤ α) :
    (∑ a : ZMod M, mass a *
      ‖∑ i : Fin N, w i *
        ZMod.stdAddChar (((h : ZMod M) * (b : ZMod M)^i.val) * a)‖^2) /
        (N : ℝ)^2 ≤ α * (1 + (K : ℝ)) := by
  classical
  let P := orderOf (ZMod.unitOfCoprime b hc)
  let r : Fin N → ZMod M := fun i => (h : ZMod M) * (b : ZMod M)^i.val
  let F : ZMod M → ℂ := fun a => ∑ i, w i * ZMod.stdAddChar (r i * a)
  change (∑ a, mass a * ‖F a‖^2) / (N : ℝ)^2 ≤ _
  have hcoll : ∀ i j, r i = r j ↔ j.val % P = i.val % P :=
    fun i j => orbit_collision_iff M b h i.val j.val hM hc
  have henergy := CLN03.finite_energy_bound N P M r w F hw hcoll
    (CLN02.collision_energy r w)
  exact CLN03.conditional_second_moment N P M K hN hMN hMP mass
    (fun a => ‖F a‖^2) α hα hmass (fun a => sq_nonneg _) henergy

/-- The real Weyl phase is the complex exponential with a real argument
multiplied by 2*pi*i. -/
noncomputable def realPhase (x : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))

theorem realPhase_norm (x : ℝ) : ‖realPhase x‖ = 1 := by
  rw [realPhase, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- A genuine real prefix/tail split has exactly the Fourier phase used
above. The integer frequency can have either sign. -/
theorem phase_prefix_tail (M : ℕ) [NeZero M] (u a : ℤ) (T : ℝ) :
    realPhase ((u : ℝ) * ((a : ℝ) / (M : ℝ) + T)) =
      realPhase ((u : ℝ) * T) *
        ZMod.stdAddChar (((u : ZMod M) * (a : ZMod M))) := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  rw [← Int.cast_mul, ZMod.stdAddChar_coe]
  unfold realPhase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

#print axioms realPhase_norm
#print axioms phase_prefix_tail
#print axioms gcd_cancel_iff
#print axioms pow_collision_iff
#print axioms orbit_collision_iff
#print axioms principal_composite_divisibility
#print axioms source_power_period_bound
#print axioms orbit_second_moment

end CLN05

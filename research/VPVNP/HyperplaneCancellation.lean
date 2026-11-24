import BinaryWalsh

/-!
VPVNP-02D: finite binary hyperplanes and final-column character cancellation.
The uniform ordered-frame distribution remains a separate obligation.
-/
open scoped BigOperators
open Finset
namespace VPVNP.Binary

section Hyperplanes
variable {I : Type*} [Fintype I] [DecidableEq I]

def parityKernel (b : Bits I) : Finset (Bits I) :=
  univ.filter (fun a => parityPair b a = 0)

def parityOutside (b : Bits I) : Finset (Bits I) :=
  univ.filter (fun a => parityPair b a ≠ 0)

@[simp] theorem mem_parityKernel (b a : Bits I) :
    a ∈ parityKernel b ↔ parityPair b a = 0 := by
  simp [parityKernel]

@[simp] theorem mem_parityOutside (b a : Bits I) :
    a ∈ parityOutside b ↔ parityPair b a ≠ 0 := by
  simp [parityOutside]

theorem kernel_injective : Function.Injective (parityKernel (I := I)) := by
  intro b c h
  funext i
  have he : b i = 0 ↔ c i = 0 := by
    have hm : unitBit i ∈ parityKernel b ↔ unitBit i ∈ parityKernel c := by rw [h]
    simpa only [mem_parityKernel, pairing_unit] using hm
  rcases bit_cases (b i) with hb | hb
  · exact hb.trans (he.mp hb).symm
  · have hc : c i ≠ 0 := by
      intro hz
      have h0 := he.mpr hz
      rw [hb] at h0
      exact one_ne_zero h0
    rcases bit_cases (c i) with hc0 | hc1
    · exact False.elim (hc hc0)
    · exact hb.trans hc1.symm

def parityHyperplanes : Finset (Finset (Bits I)) :=
  (univ.erase (0 : Bits I)).image parityKernel

theorem hyperplane_count :
    (parityHyperplanes (I := I)).card = Fintype.card (Bits I) - 1 := by
  classical
  unfold parityHyperplanes
  rw [Finset.card_image_of_injective _ kernel_injective,
      Finset.card_erase_of_mem (mem_univ _), Finset.card_univ]

theorem pairing_zero_left (a : Bits I) : parityPair 0 a = 0 := by
  simp [parityPair]

theorem pairing_detects_zero (d : Bits I) (h : ∀ a, parityPair d a = 0) : d=0 := by
  funext i
  simpa only [pairing_unit] using h (unitBit i)

theorem exists_pairing_one (b : Bits I) (hb : b ≠ 0) :
    ∃ a, parityPair b a = 1 := by
  classical
  by_contra h
  apply hb
  apply pairing_detects_zero
  intro a
  rcases bit_cases (parityPair b a) with ha | ha
  · exact ha
  · exact False.elim (h ⟨a,ha⟩)

/-- A binary functional vanishing on a nonzero functional's kernel
is zero or that functional. -/
theorem kernel_annihilator (b d : Bits I) (hb : b ≠ 0)
    (hker : ∀ a, parityPair b a = 0 → parityPair d a = 0) :
    d=0 ∨ d=b := by
  obtain ⟨v,hv⟩ := exists_pairing_one b hb
  have hone : ∀ a, parityPair b a = 1 → parityPair d a = parityPair d v := by
    intro a ha
    have hsum : parityPair b (a+v)=0 := by
      rw [pairing_add_right, ha, hv, bit_double]
    have hdz := hker (a+v) hsum
    rw [pairing_add_right] at hdz
    exact bit_sum_zero _ _ hdz
  rcases bit_cases (parityPair d v) with hd | hd
  · left
    apply pairing_detects_zero
    intro a
    rcases bit_cases (parityPair b a) with ha | ha
    · exact hker a ha
    · exact (hone a ha).trans hd
  · right
    funext i
    have he : parityPair d (unitBit i) = parityPair b (unitBit i) := by
      rcases bit_cases (parityPair b (unitBit i)) with ha | ha
      · exact (hker _ ha).trans ha.symm
      · exact (hone _ ha).trans (hd.trans ha.symm)
    simpa only [pairing_unit] using he

theorem kernel_separates (b c : Bits I) (hb : b ≠ 0) (hc : c ≠ 0)
    (hne : b ≠ c) :
    ∃ t, parityPair b t = 0 ∧ parityPair c t = 1 := by
  classical
  by_contra h
  have hker : ∀ a, parityPair b a = 0 → parityPair c a = 0 := by
    intro a ha
    rcases bit_cases (parityPair c a) with hz | ho
    · exact hz
    · exact False.elim (h ⟨a,ha,ho⟩)
  rcases kernel_annihilator b c hb hker with h0 | heq
  · exact hc h0
  · exact hne heq.symm

noncomputable def outsideWeight (b c a : Bits I) : ℝ :=
  if parityPair b a = 0 then 0 else walsh c a

theorem outsideWeight_sum (b c : Bits I) :
    (∑ a : Bits I, outsideWeight b c a) =
      ∑ a ∈ parityOutside b, walsh c a := by
  classical
  unfold parityOutside outsideWeight
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hz : parityPair b a = 0 <;> simp [hz]

/-- A translation in K_b with odd c-pairing cancels the complementary coset. -/
theorem outside_cancel (b c : Bits I) (hb : b ≠ 0) (hc : c ≠ 0)
    (hne : b ≠ c) : (∑ a ∈ parityOutside b, walsh c a) = 0 := by
  classical
  obtain ⟨t,ht,htc⟩ := kernel_separates b c hb hc hne
  have hsign : walsh c t = -1 := by simp [walsh, bitSign, htc]
  have hneg : ∀ a : Bits I, outsideWeight b c (a+t) = -outsideWeight b c a := by
    intro a
    unfold outsideWeight
    rw [pairing_add_right, ht, add_zero, walsh_add_right, hsign]
    split <;> ring
  have hshift : (∑ a : Bits I, outsideWeight b c (a+t)) =
      ∑ a : Bits I, outsideWeight b c a :=
    Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)
  simp_rw [hneg, Finset.sum_neg_distrib] at hshift
  have hzero : (∑ a : Bits I, outsideWeight b c a) = 0 := by linarith
  rwa [outsideWeight_sum] at hzero

theorem outside_same (b : Bits I) :
    (∑ a ∈ parityOutside b, walsh b a) = -( (parityOutside b).card : ℝ) := by
  classical
  calc
    (∑ a ∈ parityOutside b, walsh b a) = ∑ a ∈ parityOutside b, (-1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [walsh, bitSign, (mem_parityOutside b a).mp ha]
    _ = _ := by simp

theorem outside_nonempty (b : Bits I) (hb : b ≠ 0) : (parityOutside b).Nonempty := by
  obtain ⟨a,ha⟩ := exists_pairing_one b hb
  exact ⟨a, (mem_parityOutside b a).2 (by rw [ha]; exact one_ne_zero)⟩

/-- The two cosets have exactly equal size, in real arithmetic. -/
theorem outside_half (b : Bits I) (hb : b ≠ 0) :
    2 * ((parityOutside b).card : ℝ) = (Fintype.card (Bits I) : ℝ) := by
  classical
  have hpoint : ∀ a : Bits I, walsh b a = 1 - 2 * (if a ∈ parityOutside b then (1:ℝ) else 0) := by
    intro a
    by_cases hz : parityPair b a = 0 <;> simp [walsh, bitSign, hz]
  have hs := walsh_sum_zero b hb
  simp_rw [hpoint] at hs
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hcount : (∑ a : Bits I, if a ∈ parityOutside b then (1:ℝ) else 0) =
      ((parityOutside b).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hcount] at hs
  simpa using (sub_eq_zero.mp (by simpa using hs)).symm

noncomputable def finalMean (b c : Bits I) : ℝ :=
  (∑ a ∈ parityOutside b, walsh c a) / ((parityOutside b).card : ℝ)

/-- Exact final-column mean, indexed by the nonzero parity normals. -/
theorem final_mean (b c : Bits I) (hb : b ≠ 0) (hc : c ≠ 0) :
    finalMean b c = if b=c then -1 else 0 := by
  classical
  unfold finalMean
  by_cases he : b=c
  · subst c
    rw [if_pos rfl, outside_same]
    have hp : 0 < (parityOutside b).card := Finset.card_pos.mpr (outside_nonempty b hb)
    have hne : ((parityOutside b).card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
    exact (div_eq_iff hne).2 (by ring)
  · rw [if_neg he, outside_cancel b c hb hc he, zero_div]

/-- Uniform hyperplane mixture: only the matching normal survives.
The conditional mean g is arbitrary; the ordered-frame law must still
be related to this uniform mixture. -/
theorem uniform_normal_reduction (c : Bits I) (hc : c ≠ 0) (g : Bits I → ℝ) :
    (∑ b ∈ (univ.erase (0 : Bits I)), g b * finalMean b c) /
      ((Fintype.card (Bits I) : ℝ)-1) =
      -g c / ((Fintype.card (Bits I) : ℝ)-1) := by
  classical
  congr 1
  rw [Finset.sum_eq_single c]
  · rw [final_mean c c hc hc, if_pos rfl]
    ring
  · intro b hb hne
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    rw [final_mean b c hb0 hc, if_neg hne, mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_erase.mpr ⟨hc,mem_univ _⟩))

/-- Independence transfers under restriction: an independent list of remaining
normals together with b has no nontrivial linear combination vanishing on K_b.
The hypothesis is expressed for arbitrary coefficient combinations d. -/
theorem restriction_detects_zero (b d : Bits I) (hb : b ≠ 0) (hdb : d ≠ b)
    (hker : ∀ a, parityPair b a = 0 → parityPair d a = 0) : d=0 := by
  rcases kernel_annihilator b d hb hker with h | h
  · exact h
  · exact False.elim (hdb h)

end Hyperplanes
end VPVNP.Binary

#print axioms VPVNP.Binary.kernel_injective
#print axioms VPVNP.Binary.hyperplane_count
#print axioms VPVNP.Binary.kernel_annihilator
#print axioms VPVNP.Binary.kernel_separates
#print axioms VPVNP.Binary.outside_cancel
#print axioms VPVNP.Binary.outside_same
#print axioms VPVNP.Binary.outside_half
#print axioms VPVNP.Binary.final_mean
#print axioms VPVNP.Binary.uniform_normal_reduction
#print axioms VPVNP.Binary.restriction_detects_zero

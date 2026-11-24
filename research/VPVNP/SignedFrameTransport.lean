import OrderedFrameFibers

/-! VPVNP-02F: signed transport over actual frame fibers. -/
open scoped BigOperators
open Finset
namespace VPVNP.Binary

noncomputable section

abbrev NonzeroNormal (n : ℕ) := {b : BinarySpace (n+1) // b ≠ 0}
abbrev KernelFrames (n : ℕ) (b : BinarySpace (n+1)) :=
  BinarySpace n ≃ₗ[ZMod 2] KernelSpace b

local instance equivFintype {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Finite V] [Finite W] :
    Fintype (V ≃ₗ[ZMod 2] W) := by
  letI : Finite (V ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] W => (e : V → W)) (by
      intro e f h
      ext x
      exact congrFun h x)
  exact Fintype.ofFinite _

local instance normalFintype (n : ℕ) : Fintype (NonzeroNormal n) := Fintype.ofFinite _
local instance frameFiberFintype (n : ℕ) (b : BinarySpace (n+1)) :
    Fintype (FrameFiber n b) := Fintype.ofFinite _
local instance outsideFintype (n : ℕ) (b : BinarySpace (n+1)) :
    Fintype (OutsideSpace b) := Fintype.ofFinite _

/-- Partition all full frames by the unique nonzero last normal. -/
def normalPartition (n : ℕ) :
    OrderedFrame n ≃ (Σ b : NonzeroNormal n, FrameFiber n b.1) :=
  (Equiv.ofBijective
    (fun p : Σ b : NonzeroNormal n, FrameFiber n b.1 => p.2.1)
    (by
      constructor
      · rintro ⟨b,e⟩ ⟨c,f⟩ he
        have hbc : b=c := by
          apply Subtype.ext
          have h1 := frame_normal_unique e.1 b.1 e.2
          have h2 := frame_normal_unique f.1 c.1 f.2
          rw [he] at h1
          exact h1.trans h2.symm
        subst c
        have hef : e=f := Subtype.ext he
        subst f
        rfl
      · intro e
        exact ⟨⟨⟨frameNormal e, frame_normal_nonzero e⟩,⟨e,frame_normal_equation e⟩⟩,rfl⟩)).symm

theorem partition_card (n : ℕ) :
    Fintype.card (OrderedFrame n) =
      ∑ b : NonzeroNormal n, Fintype.card (FrameFiber n b.1) := by
  rw [Fintype.card_congr (normalPartition n), Fintype.card_sigma]

theorem normal_card (n : ℕ) :
    Fintype.card (NonzeroNormal n) = Fintype.card (BinarySpace (n+1))-1 := by
  classical
  calc
    Fintype.card (NonzeroNormal n) = (univ.erase (0 : BinarySpace (n+1))).card :=
      Fintype.card_of_subtype _ (fun x => by simp)
    _ = _ := by rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ]

theorem frame_card {n : ℕ} (c : BinarySpace (n+1)) (hc : c ≠ 0) :
    Fintype.card (OrderedFrame n) =
      Fintype.card (NonzeroNormal n) *
        (Fintype.card (KernelFrames n c) * Fintype.card (OutsideSpace c)) := by
  classical
  rw [partition_card]
  have hcard (b : NonzeroNormal n) :
      Fintype.card (FrameFiber n b.1) = Fintype.card (FrameFiber n c) :=
    Fintype.card_congr ((commonFiber b.1 b.2).trans (commonFiber c hc).symm)
  simp_rw [hcard]
  rw [Fintype.card_congr (frameFiberEquiv c), Fintype.card_prod]
  simp

def prefixSign {n : ℕ} {b : BinarySpace (n+1)}
    (a : Fin n → BinarySpace (n+1)) (h : KernelFrames n b) : ℝ :=
  ∏ i : Fin n, walsh (a i) (h (unitBit i)).1

def frameSign {n : ℕ} (a : Fin n → BinarySpace (n+1))
    (c : BinarySpace (n+1)) (e : OrderedFrame n) : ℝ :=
  (∏ i : Fin n, walsh (a i) (e (unitBit i,0))) * walsh c (e (0,1))

theorem frame_sum_partition {n : ℕ} (g : OrderedFrame n → ℝ) :
    (∑ e : OrderedFrame n, g e) =
      ∑ b : NonzeroNormal n, ∑ e : FrameFiber n b.1, g e.1 := by
  calc
    (∑ e : OrderedFrame n, g e) =
        ∑ p : (Σ b : NonzeroNormal n, FrameFiber n b.1), g p.2.1 := by
      exact (Fintype.sum_equiv (normalPartition n).symm _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_sigma _

/-- Factor prefix weight from the last vector using the actual product equivalence. -/
theorem frame_fiber_sum {n : ℕ} (a : Fin n → BinarySpace (n+1))
    (b c : BinarySpace (n+1)) :
    (∑ e : FrameFiber n b, frameSign a c e.1) =
      (∑ h : KernelFrames n b, prefixSign a h) *
        ∑ v : OutsideSpace b, walsh c v.1 := by
  calc
    (∑ e : FrameFiber n b, frameSign a c e.1) =
        ∑ p : KernelFrames n b × OutsideSpace b, prefixSign a p.1 * walsh c p.2.1 := by
      apply Fintype.sum_equiv (frameFiberEquiv b)
      intro e
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.mul_sum]

theorem outside_iff {n : ℕ} (b v : BinarySpace (n+1)) :
    v ∈ parityOutside b ↔ parityLinear b v = 1 := by
  rw [mem_parityOutside, parityLinear_apply]
  rcases bit_cases (parityPair b v) with hz | ho <;> simp [hz,ho]

theorem outside_sum_subtype {n : ℕ} (b c : BinarySpace (n+1)) :
    (∑ v : OutsideSpace b, walsh c v.1) = ∑ v ∈ parityOutside b, walsh c v :=
  (Finset.sum_subtype _ (outside_iff b) (walsh c)).symm

theorem outside_card_subtype {n : ℕ} (b : BinarySpace (n+1)) :
    Fintype.card (OutsideSpace b) = (parityOutside b).card :=
  Fintype.card_of_subtype _ (outside_iff b)

theorem off_fiber_zero {n : ℕ} (a : Fin n → BinarySpace (n+1))
    (b c : BinarySpace (n+1)) (hb : b ≠ 0) (hc : c ≠ 0) (hne : b ≠ c) :
    (∑ e : FrameFiber n b, frameSign a c e.1) = 0 := by
  rw [frame_fiber_sum, outside_sum_subtype, outside_cancel b c hb hc hne, mul_zero]

theorem on_fiber_sign {n : ℕ} (a : Fin n → BinarySpace (n+1))
    (c : BinarySpace (n+1)) :
    (∑ e : FrameFiber n c, frameSign a c e.1) =
      -(Fintype.card (OutsideSpace c) : ℝ) *
        ∑ h : KernelFrames n c, prefixSign a h := by
  rw [frame_fiber_sum, outside_sum_subtype, outside_same, outside_card_subtype]
  ring

/-- Nonzero last normal: all other actual fibers contribute zero. -/
theorem global_signed_sum {n : ℕ} (a : Fin n → BinarySpace (n+1))
    (c : BinarySpace (n+1)) (hc : c ≠ 0) :
    (∑ e : OrderedFrame n, frameSign a c e) =
      -(Fintype.card (OutsideSpace c) : ℝ) *
        ∑ h : KernelFrames n c, prefixSign a h := by
  classical
  rw [frame_sum_partition]
  rw [Finset.sum_eq_single (⟨c,hc⟩ : NonzeroNormal n)]
  · exact on_fiber_sign a c
  · intro b hb hne
    exact off_fiber_zero a b.1 c b.2 hc (fun he => hne (Subtype.ext he))
  · simp

def frameAverage {n : ℕ} (a : Fin n → BinarySpace (n+1))
    (c : BinarySpace (n+1)) : ℝ :=
  (∑ e : OrderedFrame n, frameSign a c e) / Fintype.card (OrderedFrame n)

def kernelAverage {n : ℕ} (a : Fin n → BinarySpace (n+1))
    (c : BinarySpace (n+1)) : ℝ :=
  (∑ h : KernelFrames n c, prefixSign a h) / Fintype.card (KernelFrames n c)

/-- Actual normalized recurrence to the restricted kernel-basis distribution.
The next step identifies that distribution with a canonical dual-rank character. -/
theorem actual_frame_reduction {n : ℕ} (a : Fin n → BinarySpace (n+1))
    (c : BinarySpace (n+1)) (hc : c ≠ 0) :
    frameAverage a c = -kernelAverage a c / (Fintype.card (NonzeroNormal n) : ℝ) := by
  have hN : 0 < Fintype.card (NonzeroNormal n) :=
    Fintype.card_pos_iff.mpr ⟨⟨c,hc⟩⟩
  have hK : 0 < Fintype.card (KernelFrames n c) :=
    Fintype.card_pos_iff.mpr ⟨kernelCoordinates c hc⟩
  have hO : 0 < Fintype.card (OutsideSpace c) :=
    Fintype.card_pos_iff.mpr ⟨outsidePoint c hc⟩
  have hN' : (Fintype.card (NonzeroNormal n) : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hK' : (Fintype.card (KernelFrames n c) : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hO' : (Fintype.card (OutsideSpace c) : ℝ) ≠ 0 := by exact_mod_cast hO.ne'
  unfold frameAverage kernelAverage
  rw [global_signed_sum a c hc, frame_card c hc]
  push_cast
  field_simp [hN',hK',hO'] <;> ring

end
end VPVNP.Binary

#print axioms VPVNP.Binary.normalPartition
#print axioms VPVNP.Binary.partition_card
#print axioms VPVNP.Binary.normal_card
#print axioms VPVNP.Binary.frame_card
#print axioms VPVNP.Binary.frame_sum_partition
#print axioms VPVNP.Binary.frame_fiber_sum
#print axioms VPVNP.Binary.outside_sum_subtype
#print axioms VPVNP.Binary.off_fiber_zero
#print axioms VPVNP.Binary.on_fiber_sign
#print axioms VPVNP.Binary.global_signed_sum
#print axioms VPVNP.Binary.actual_frame_reduction

import HyperplaneCancellation

/-! VPVNP-02E: actual ordered-frame fibers, linear forms, and uniformity. -/
open scoped BigOperators
open Finset
namespace VPVNP.Binary

section Forms
variable {I : Type*} [Fintype I] [DecidableEq I]

def parityLinear (b : Bits I) : Bits I →ₗ[ZMod 2] ZMod 2 where
  toFun := parityPair b
  map_add' := pairing_add_right b
  map_smul' r a := by
    change parityPair b (r • a) = r * parityPair b a
    unfold parityPair
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change b i * (r * a i) = r * (b i * a i)
    ring

@[simp] theorem parityLinear_apply (b a : Bits I) :
    parityLinear b a = parityPair b a := rfl

def formNormal (f : Bits I →ₗ[ZMod 2] ZMod 2) : Bits I :=
  fun i => f (unitBit i)

theorem unit_expansion (a : Bits I) :
    a = ∑ i : I, a i • unitBit i := by
  classical
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [unitBit]
  · intro i hi hij
    simp [unitBit, Ne.symm hij]
  · simp

theorem normal_represents (f : Bits I →ₗ[ZMod 2] ZMod 2) (a : Bits I) :
    parityPair (formNormal f) a = f a := by
  calc
    parityPair (formNormal f) a = ∑ i : I, a i * f (unitBit i) := by
      unfold parityPair formNormal
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = f (∑ i : I, a i • unitBit i) := by
      simp [map_sum, map_smul, smul_eq_mul]
    _ = f a := by rw [← unit_expansion a]

theorem normal_unique (b c : Bits I)
    (h : ∀ a, parityPair b a = parityPair c a) : b=c := by
  funext i
  simpa only [pairing_unit] using h (unitBit i)

theorem parity_surjective (b : Bits I) (hb : b ≠ 0) :
    Function.Surjective (parityLinear b) := by
  obtain ⟨v,hv⟩ := exists_pairing_one b hb
  intro t
  rcases bit_cases t with rfl | rfl
  · exact ⟨0, (parityLinear b).map_zero⟩
  · exact ⟨v,hv⟩

end Forms

abbrev BinarySpace (n : ℕ) := Bits (Fin n)
abbrev OrderedFrame (n : ℕ) :=
  (BinarySpace n × ZMod 2) ≃ₗ[ZMod 2] BinarySpace (n+1)

abbrev FrameFiber (n : ℕ) (b : BinarySpace (n+1)) :=
  {e : OrderedFrame n // ∀ p, parityLinear b (e p) = p.2}

abbrev KernelSpace {n : ℕ} (b : BinarySpace (n+1)) :=
  LinearMap.ker (parityLinear b)

abbrev OutsideSpace {n : ℕ} (b : BinarySpace (n+1)) :=
  {v : BinarySpace (n+1) // parityLinear b v = 1}

/-- The last coordinate of the inverse frame is a linear functional. -/
def frameNormal {n : ℕ} (e : OrderedFrame n) : BinarySpace (n+1) :=
  formNormal ((LinearMap.snd (ZMod 2) (BinarySpace n) (ZMod 2)).comp e.symm.toLinearMap)

theorem frame_normal_equation {n : ℕ} (e : OrderedFrame n)
    (p : BinarySpace n × ZMod 2) :
    parityLinear (frameNormal e) (e p) = p.2 := by
  simp [frameNormal, normal_represents]

theorem frame_normal_nonzero {n : ℕ} (e : OrderedFrame n) : frameNormal e ≠ 0 := by
  intro h
  have he := frame_normal_equation e (0,1)
  rw [h, parityLinear_apply, pairing_zero_left] at he
  exact zero_ne_one he

theorem frame_normal_unique {n : ℕ} (e : OrderedFrame n) (b : BinarySpace (n+1))
    (h : ∀ p, parityLinear b (e p) = p.2) :
    b = frameNormal e := by
  apply normal_unique
  intro a
  have h1 := h (e.symm a)
  have h2 := frame_normal_equation e (e.symm a)
  rw [e.apply_symm_apply] at h1 h2
  exact h1.trans h2.symm

theorem kernel_finrank {n : ℕ} (b : BinarySpace (n+1)) (hb : b ≠ 0) :
    Module.finrank (ZMod 2) (KernelSpace b) = n := by
  have h := (parityLinear b).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (parity_surjective b hb)] at h
  simp only [finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  change Module.finrank (ZMod 2) (LinearMap.ker (parityLinear b)) = n
  omega

noncomputable def kernelCoordinates {n : ℕ} (b : BinarySpace (n+1)) (hb : b ≠ 0) :
    BinarySpace n ≃ₗ[ZMod 2] KernelSpace b :=
  LinearEquiv.ofFinrankEq (BinarySpace n) (KernelSpace b) (by rw [Module.finrank_fin_fun, kernel_finrank b hb])

noncomputable def outsidePoint {n : ℕ} (b : BinarySpace (n+1)) (hb : b ≠ 0) :
    OutsideSpace b :=
  ⟨Classical.choose (exists_pairing_one b hb), Classical.choose_spec (exists_pairing_one b hb)⟩

/-- The prefix of a frame in a normal fiber is an actual basis of its kernel. -/
def prefixLinear {n : ℕ} {b : BinarySpace (n+1)} (e : FrameFiber n b) :
    BinarySpace n →ₗ[ZMod 2] KernelSpace b where
  toFun u := ⟨e.1 (u,0), e.2 (u,0)⟩
  map_add' x y := by
    apply Subtype.ext
    change e.1 (x+y,0) = e.1 (x,0) + e.1 (y,0)
    rw [← map_add]
    congr 1 <;> simp
  map_smul' r x := by
    apply Subtype.ext
    change e.1 (r • x,0) = r • e.1 (x,0)
    rw [← map_smul]
    congr 1 <;> simp

noncomputable def prefixEquiv {n : ℕ} {b : BinarySpace (n+1)} (e : FrameFiber n b) :
    BinarySpace n ≃ₗ[ZMod 2] KernelSpace b :=
  LinearEquiv.ofBijective (prefixLinear e) (by
    constructor
    · intro x y h
      have he : e.1 (x,0) = e.1 (y,0) := congrArg Subtype.val h
      exact congrArg Prod.fst (e.1.injective he)
    · intro x
      let p := e.1.symm x.1
      have hp : p.2 = 0 := by
        rw [← e.2 p]
        change parityLinear b (e.1 (e.1.symm x.1)) = 0
        rw [e.1.apply_symm_apply]
        exact x.2
      refine ⟨p.1, Subtype.ext ?_⟩
      change e.1 (p.1,0) = x.1
      rw [← hp]
      exact e.1.apply_symm_apply x.1)

def finalVector {n : ℕ} {b : BinarySpace (n+1)} (e : FrameFiber n b) : OutsideSpace b :=
  ⟨e.1 (0,1), e.2 (0,1)⟩

/-- Construct a full frame from a kernel basis and a final vector outside the kernel. -/
def extendLinear {n : ℕ} {b : BinarySpace (n+1)}
    (h : BinarySpace n ≃ₗ[ZMod 2] KernelSpace b) (v : OutsideSpace b) :
    (BinarySpace n × ZMod 2) →ₗ[ZMod 2] BinarySpace (n+1) where
  toFun p := (h p.1).1 + p.2 • v.1
  map_add' p q := by
    change (h (p.1+q.1)).1 + (p.2+q.2) • v.1 =
      ((h p.1).1 + p.2 • v.1) + ((h q.1).1 + q.2 • v.1)
    rw [map_add]
    change (h p.1).1 + (h q.1).1 + (p.2+q.2) • v.1 = _
    module
  map_smul' r p := by
    change (h (r • p.1)).1 + (r*p.2) • v.1 = r • ((h p.1).1 + p.2 • v.1)
    rw [map_smul]
    change r • (h p.1).1 + (r*p.2) • v.1 = _
    rw [smul_add, mul_smul]

theorem extend_pairing {n : ℕ} {b : BinarySpace (n+1)}
    (h : BinarySpace n ≃ₗ[ZMod 2] KernelSpace b) (v : OutsideSpace b)
    (p : BinarySpace n × ZMod 2) : parityLinear b (extendLinear h v p) = p.2 := by
  change parityLinear b ((h p.1).1 + p.2 • v.1) = p.2
  rw [map_add, map_smul, (h p.1).2, v.2]
  simp

noncomputable def extendFrame {n : ℕ} {b : BinarySpace (n+1)}
    (h : BinarySpace n ≃ₗ[ZMod 2] KernelSpace b) (v : OutsideSpace b) :
    FrameFiber n b := by
  have bij : Function.Bijective (extendLinear h v) := by
    constructor
    · intro p q hpq
      have ht : p.2 = q.2 := by
        have he := congrArg (parityLinear b) hpq
        simpa only [extend_pairing] using he
      have he : (h p.1).1 + p.2 • v.1 = (h q.1).1 + q.2 • v.1 := hpq
      rw [ht] at he
      exact Prod.ext (h.injective (Subtype.ext (add_right_cancel he))) ht
    · intro x
      let t := parityLinear b x
      have hx : x - t • v.1 ∈ LinearMap.ker (parityLinear b) := by
        change parityLinear b (x-t • v.1) = 0
        rw [map_sub, map_smul, v.2]
        simp [t]
      let w : KernelSpace b := ⟨x-t • v.1,hx⟩
      refine ⟨(h.symm w,t), ?_⟩
      change (h (h.symm w)).1 + t • v.1 = x
      rw [h.apply_symm_apply]
      change x-t • v.1+t • v.1 = x
      abel
  let e := LinearEquiv.ofBijective (extendLinear h v) bij
  exact ⟨e, extend_pairing h v⟩

/-- Explicit bijection: the prefix and last vector determine the frame. -/
noncomputable def frameFiberEquiv {n : ℕ} (b : BinarySpace (n+1)) :
    FrameFiber n b ≃ ((BinarySpace n ≃ₗ[ZMod 2] KernelSpace b) × OutsideSpace b) where
  toFun e := (prefixEquiv e, finalVector e)
  invFun p := extendFrame p.1 p.2
  left_inv e := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro p
    change e.1 (p.1,0) + p.2 • e.1 (0,1) = e.1 p
    rw [← map_smul, ← map_add]
    congr 1
    ext <;> simp
  right_inv p := by
    apply Prod.ext
    · apply LinearEquiv.ext
      intro x
      apply Subtype.ext
      change (p.1 x).1 + (0:ZMod 2) • p.2.1 = (p.1 x).1
      simp
    · apply Subtype.ext
      change (p.1 0).1 + (1:ZMod 2) • p.2.1 = p.2.1
      simp

noncomputable def outsideEquivKernel {n : ℕ} {b : BinarySpace (n+1)}
    (v : OutsideSpace b) : OutsideSpace b ≃ KernelSpace b where
  toFun x := ⟨x.1-v.1, by change parityLinear b (x.1-v.1)=0; rw [map_sub,x.2,v.2,sub_self]⟩
  invFun x := ⟨x.1+v.1, by change parityLinear b (x.1+v.1)=1; rw [map_add,x.2,v.2,zero_add]⟩
  left_inv x := Subtype.ext (sub_add_cancel x.1 v.1)
  right_inv x := Subtype.ext (add_sub_cancel_right x.1 v.1)

/-- Every normal fiber is equivalent to the same product of smaller frames and
vectors.  This is the uniform hyperplane sampling law at the counting level. -/
noncomputable def commonFiber {n : ℕ} (b : BinarySpace (n+1)) (hb : b ≠ 0) :
    FrameFiber n b ≃ ((BinarySpace n ≃ₗ[ZMod 2] BinarySpace n) × BinarySpace n) := by
  let k := kernelCoordinates b hb
  let v := outsidePoint b hb
  let eh : (BinarySpace n ≃ₗ[ZMod 2] KernelSpace b) ≃
      (BinarySpace n ≃ₗ[ZMod 2] BinarySpace n) :=
    { toFun := fun h => h.trans k.symm
      invFun := fun h => h.trans k
      left_inv := by intro h; ext x; simp
      right_inv := by intro h; ext x; simp }
  exact (frameFiberEquiv b).trans
    (Equiv.prodCongr eh ((outsideEquivKernel v).trans k.symm.toEquiv))

theorem uniform_fiber_card {n : ℕ} (b c : BinarySpace (n+1))
    (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.card (FrameFiber n b) = Nat.card (FrameFiber n c) :=
  Nat.card_congr ((commonFiber b hb).trans (commonFiber c hc).symm)

theorem frame_fiber_nonempty {n : ℕ} (b : BinarySpace (n+1)) (hb : b ≠ 0) :
    Nonempty (FrameFiber n b) :=
  ⟨(commonFiber b hb).symm (LinearEquiv.refl (ZMod 2) (BinarySpace n),0)⟩

end VPVNP.Binary

#print axioms VPVNP.Binary.normal_represents
#print axioms VPVNP.Binary.normal_unique
#print axioms VPVNP.Binary.frame_normal_equation
#print axioms VPVNP.Binary.frame_normal_nonzero
#print axioms VPVNP.Binary.frame_normal_unique
#print axioms VPVNP.Binary.kernel_finrank
#print axioms VPVNP.Binary.prefixEquiv
#print axioms VPVNP.Binary.extendFrame
#print axioms VPVNP.Binary.frameFiberEquiv
#print axioms VPVNP.Binary.commonFiber
#print axioms VPVNP.Binary.uniform_fiber_card
#print axioms VPVNP.Binary.frame_fiber_nonempty

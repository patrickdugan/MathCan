import MatrixRankCharacter

/-!
VPVNP-02H: canonical diagonal recurrence on actual matrix units.
The last k marked coordinates give a representative whose final coordinate
can be removed by the signed ordered-frame reduction.
-/

open scoped BigOperators
open Finset
namespace VPVNP.Binary

noncomputable section

attribute [local instance] equivFintype normalFintype frameFiberFintype outsideFintype unitMatrixFintype

def tailMark (n k : ℕ) (i : Fin n) : ZMod 2 :=
  if n ≤ i.val+k then 1 else 0

def tailMatrix (n k : ℕ) : BinMat (Fin n) := Matrix.diagonal (tailMark n k)

theorem tailMark_zero (n : ℕ) (i : Fin n) : tailMark n 0 i = 0 := by
  simp [tailMark, Nat.not_le_of_lt i.isLt]

theorem tailMark_castSucc (n k : ℕ) (i : Fin n) :
    tailMark (n+1) (k+1) i.castSucc = tailMark n k i := by
  unfold tailMark
  have h : n+1 ≤ i.castSucc.val+(k+1) ↔ n ≤ i.val+k := by
    simp only [Fin.val_castSucc]
    omega
  simp only [h]

theorem tailMark_last (n k : ℕ) : tailMark (n+1) (k+1) (Fin.last n) = 1 := by
  unfold tailMark
  have h : n+1 ≤ (Fin.last n).val+(k+1) := by simp only [Fin.val_last]; omega
  rw [if_pos h]

theorem tailMark_nonzero (n k : ℕ) (i : Fin n) :
    tailMark n k i ≠ 0 ↔ n ≤ i.val+k := by
  unfold tailMark
  by_cases h : n ≤ i.val+k <;> simp [h]

def tailIndexEquiv (n k : ℕ) (hk : k ≤ n) :
    Fin k ≃ {i : Fin n // tailMark n k i ≠ 0} where
  toFun j :=
    ⟨⟨n-k+j.val, by have := j.isLt; omega⟩,
      (tailMark_nonzero n k _).2 (by change n ≤ n-k+j.val+k; omega)⟩
  invFun i := ⟨i.1.val-(n-k), by
    have h := (tailMark_nonzero n k i.1).1 i.2
    have hi := i.1.isLt
    omega⟩
  left_inv j := by
    apply Fin.ext
    change n-k+j.val-(n-k) = j.val
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change n-k+(i.1.val-(n-k)) = i.1.val
    have h := (tailMark_nonzero n k i.1).1 i.2
    omega

theorem tailMatrix_rank (n k : ℕ) (hk : k ≤ n) :
    (tailMatrix n k).rank = k := by
  unfold tailMatrix
  rw [Matrix.rank_diagonal]
  exact (Fintype.card_congr (tailIndexEquiv n k hk).symm).trans (Fintype.card_fin k)

/-- Split a binary vector into its prefix and last coordinate. -/
def joinLast (n : ℕ) :
    (BinarySpace n × ZMod 2) ≃ₗ[ZMod 2] BinarySpace (n+1) where
  toFun p := Fin.snoc p.1 p.2
  invFun x := (Fin.init x, x (Fin.last n))
  left_inv p := by simp
  right_inv x := Fin.snoc_init_self x
  map_add' p q := by
    funext i
    cases i using Fin.lastCases <;> simp
  map_smul' r p := by
    funext i
    cases i using Fin.lastCases <;> simp

theorem joinLast_prefix_unit (n : ℕ) (i : Fin n) :
    joinLast n (unitBit i,0) = unitBit i.castSucc := by
  funext j
  cases j using Fin.lastCases with
  | last =>
    have h : Fin.last n ≠ i.castSucc := by
      intro e
      have he := congrArg Fin.val e
      simp only [Fin.val_last, Fin.val_castSucc] at he
      have hi := i.isLt
      omega
    simp [joinLast, unitBit, h]
  | cast j => simp [joinLast, unitBit, Fin.castSucc_inj]

theorem joinLast_last_unit (n : ℕ) :
    joinLast n (0,1) = unitBit (Fin.last n) := by
  funext j
  cases j using Fin.lastCases <;> simp [joinLast, unitBit]

theorem lastNormal_pair (n : ℕ) (x : BinarySpace (n+1)) :
    parityPair (unitBit (Fin.last n)) x = x (Fin.last n) := by
  rw [pairing_symm, pairing_unit]

theorem lastNormal_ne_zero (n : ℕ) :
    unitBit (Fin.last n) ≠ (0 : BinarySpace (n+1)) := by
  intro h
  have he := congrFun h (Fin.last n)
  simpa [unitBit] using he

def lastFiber (n : ℕ) : FrameFiber n (unitBit (Fin.last n)) :=
  ⟨joinLast n, by
    intro p
    change parityPair (unitBit (Fin.last n)) (Fin.snoc p.1 p.2) = p.2
    rw [lastNormal_pair, Fin.snoc_last]⟩

def lastKernel (n : ℕ) : BinarySpace n ≃ₗ[ZMod 2]
    KernelSpace (unitBit (Fin.last n)) := prefixEquiv (lastFiber n)

theorem lastKernel_apply (n : ℕ) (x : BinarySpace n) (i : Fin n) :
    (lastKernel n x).1 i.castSucc = x i := by
  change (joinLast n (x,0)) i.castSucc = x i
  simp [joinLast]

def unitAuto (n : ℕ) : MatUnits (Fin n) ≃
    (BinarySpace n ≃ₗ[ZMod 2] BinarySpace n) :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (BinarySpace n))).toEquiv

theorem unitAuto_column (n : ℕ) (W : MatUnits (Fin n)) (i j : Fin n) :
    unitAuto n W (unitBit j) i = (W : BinMat (Fin n)) i j := by
  change Matrix.mulVec (W : BinMat (Fin n)) (unitBit j) i = _
  have hu : unitBit j = Pi.single j (1 : ZMod 2) := by
    funext t
    simp [unitBit, Pi.single_apply]
  rw [hu, Matrix.mulVec_single_one]
  rfl

def unitsFrame (n : ℕ) : MatUnits (Fin (n+1)) ≃ OrderedFrame n :=
  (unitAuto (n+1)).trans
    { toFun := fun e => (joinLast n).trans e
      invFun := fun e => (joinLast n).symm.trans e
      left_inv := by intro e; ext x; simp
      right_inv := by intro e; ext x; simp }

def unitsKernel (n : ℕ) : MatUnits (Fin n) ≃
    KernelFrames n (unitBit (Fin.last n)) :=
  (unitAuto n).trans
    { toFun := fun e => e.trans (lastKernel n)
      invFun := fun e => e.trans (lastKernel n).symm
      left_inv := by intro e; ext x; simp
      right_inv := by intro e; ext x; simp }

theorem unitsFrame_prefix_column (n : ℕ) (W : MatUnits (Fin (n+1))) (i : Fin n) :
    unitsFrame n W (unitBit i,0) i.castSucc = (W : BinMat (Fin (n+1))) i.castSucc i.castSucc := by
  change unitAuto (n+1) W (joinLast n (unitBit i,0)) i.castSucc = _
  rw [joinLast_prefix_unit, unitAuto_column]

theorem unitsFrame_last_column (n : ℕ) (W : MatUnits (Fin (n+1))) :
    unitsFrame n W (0,1) (Fin.last n) = (W : BinMat (Fin (n+1))) (Fin.last n) (Fin.last n) := by
  change unitAuto (n+1) W (joinLast n (0,1)) (Fin.last n) = _
  rw [joinLast_last_unit, unitAuto_column]

theorem unitsKernel_prefix_column (n : ℕ) (W : MatUnits (Fin n)) (i : Fin n) :
    (unitsKernel n W (unitBit i)).1 i.castSucc = (W : BinMat (Fin n)) i i := by
  change (lastKernel n (unitAuto n W (unitBit i))).1 i.castSucc = _
  rw [lastKernel_apply, unitAuto_column]

theorem bitSign_sum {A : Type*} (s : Finset A) (f : A → ZMod 2) :
    bitSign (∑ i ∈ s, f i) = ∏ i ∈ s, bitSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bitSign]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, bitSign_add, ih]

theorem scalar_unit_pair {I : Type*} [Fintype I] [DecidableEq I]
    (s : ZMod 2) (i : I) (x : Bits I) :
    parityPair (s • unitBit i) x = s * x i := by
  rw [pairing_symm]
  change parityLinear x (s • unitBit i) = _
  rw [map_smul, parityLinear_apply, pairing_unit]
  rfl

def prefixNormals (n k : ℕ) (i : Fin n) : BinarySpace (n+1) :=
  tailMark n k i • unitBit i.castSucc

theorem trace_tail_product (n k : ℕ) (W : MatUnits (Fin n)) :
    traceCharacter (tailMatrix n k) (W : BinMat (Fin n)) =
      ∏ i : Fin n, bitSign (tailMark n k i * (W : BinMat (Fin n)) i i) := by
  unfold traceCharacter tailMatrix Matrix.trace
  rw [bitSign_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Matrix.diag_apply, Matrix.diagonal_mul]

theorem frame_tail_sign (n k : ℕ) (W : MatUnits (Fin (n+1))) :
    traceCharacter (tailMatrix (n+1) (k+1)) (W : BinMat (Fin (n+1))) =
      frameSign (prefixNormals n k) (unitBit (Fin.last n)) (unitsFrame n W) := by
  rw [trace_tail_product, Fin.prod_univ_castSucc]
  simp only [tailMark_castSucc, tailMark_last, one_mul]
  unfold frameSign prefixNormals walsh
  simp only [scalar_unit_pair, unitsFrame_prefix_column, lastNormal_pair, unitsFrame_last_column]

theorem kernel_tail_sign (n k : ℕ) (W : MatUnits (Fin n)) :
    traceCharacter (tailMatrix n k) (W : BinMat (Fin n)) =
      prefixSign (prefixNormals n k) (unitsKernel n W) := by
  rw [trace_tail_product]
  unfold prefixSign prefixNormals walsh
  simp only [scalar_unit_pair, unitsKernel_prefix_column]

theorem trace_tail_frame (n k : ℕ) :
    traceAverage (tailMatrix (n+1) (k+1)) =
      frameAverage (prefixNormals n k) (unitBit (Fin.last n)) := by
  unfold traceAverage frameAverage
  rw [← Fintype.card_congr (unitsFrame n)]
  congr 1
  exact Fintype.sum_equiv (unitsFrame n) _ _ (frame_tail_sign n k)

theorem trace_tail_kernel (n k : ℕ) :
    traceAverage (tailMatrix n k) =
      kernelAverage (prefixNormals n k) (unitBit (Fin.last n)) := by
  unfold traceAverage kernelAverage
  rw [← Fintype.card_congr (unitsKernel n)]
  congr 1
  exact Fintype.sum_equiv (unitsKernel n) _ _ (kernel_tail_sign n k)

theorem binary_space_card (n : ℕ) : Fintype.card (BinarySpace n) = 2^n := by
  change Fintype.card (Fin n → ZMod 2) = _
  rw [Fintype.card_pi_const, ZMod.card]

theorem normal_card_real (n : ℕ) :
    (Fintype.card (NonzeroNormal n) : ℝ) = (2:ℝ)^(n+1)-1 := by
  rw [normal_card, binary_space_card]
  have hp : 0 < (2:ℕ)^(n+1) := pow_pos (by decide) _
  have h : 1 ≤ (2:ℕ)^(n+1) := by omega
  rw [Nat.cast_sub h]
  norm_cast

/-- Actual canonical trace recurrence, obtained from the ordered frame law. -/
theorem canonical_step (n k : ℕ) :
    traceAverage (tailMatrix (n+1) (k+1)) =
      -traceAverage (tailMatrix n k) / ((2:ℝ)^(n+1)-1) := by
  rw [trace_tail_frame, actual_frame_reduction _ _ (lastNormal_ne_zero n),
      ← trace_tail_kernel, normal_card_real]

theorem canonical_zero (n : ℕ) : traceAverage (tailMatrix n 0) = 1 := by
  have h : tailMatrix n 0 = 0 := by
    ext i j
    simp [tailMatrix, tailMark_zero, Matrix.diagonal_apply]
  rw [h]
  have hc : 0 < Fintype.card (MatUnits (Fin n)) := Fintype.card_pos_iff.mpr ⟨1⟩
  have hc' : (Fintype.card (MatUnits (Fin n)) : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold traceAverage traceCharacter
  simp [bitSign, hc']

/-- The decreasing product has factors 2^n-1 through 2^(n-k+1)-1. -/
def rankValue (n k : ℕ) : ℝ :=
  (-1:ℝ)^k / ∏ i : Fin k, ((2:ℝ)^(n-i.val)-1)

theorem rankValue_zero (n : ℕ) : rankValue n 0 = 1 := by
  simp [rankValue]

theorem rankValue_step (n k : ℕ) :
    rankValue (n+1) (k+1) = -rankValue n k / ((2:ℝ)^(n+1)-1) := by
  unfold rankValue
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.succ_sub_succ_eq_sub]
  rw [pow_succ (-1:ℝ) k, mul_neg, mul_one, ← neg_div, div_div]
  rw [mul_comm ((2:ℝ)^(n+1)-1)]

theorem canonical_closed (n k : ℕ) (hk : k ≤ n) :
    traceAverage (tailMatrix n k) = rankValue n k :=
  recurrence_unique
    (fun n k => traceAverage (tailMatrix n k)) rankValue
    canonical_zero rankValue_zero canonical_step rankValue_step n k hk

/-- Closed full-rank character formula for any actual dual matrix. -/
theorem full_rank_character {n : ℕ} (B : BinMat (Fin n)) :
    traceAverage B = rankValue n B.rank := by
  have hk : B.rank ≤ n := B.rank_le_width
  calc
    traceAverage B = traceAverage (tailMatrix n B.rank) :=
      trace_average_rank_invariant _ _ (tailMatrix_rank n B.rank hk).symm
    _ = rankValue n B.rank := canonical_closed n B.rank hk

theorem full_rank_entry_character {n : ℕ} (B : BinMat (Fin n)) :
    entryAverage B = rankValue n B.rank := by
  rw [entry_average_trace, full_rank_character, Matrix.rank_transpose]

end
end VPVNP.Binary

#print axioms VPVNP.Binary.tailMatrix_rank
#print axioms VPVNP.Binary.joinLast
#print axioms VPVNP.Binary.unitsFrame
#print axioms VPVNP.Binary.unitsKernel
#print axioms VPVNP.Binary.frame_tail_sign
#print axioms VPVNP.Binary.kernel_tail_sign
#print axioms VPVNP.Binary.trace_tail_frame
#print axioms VPVNP.Binary.trace_tail_kernel
#print axioms VPVNP.Binary.normal_card_real
#print axioms VPVNP.Binary.canonical_step
#print axioms VPVNP.Binary.canonical_zero
#print axioms VPVNP.Binary.rankValue_step
#print axioms VPVNP.Binary.canonical_closed
#print axioms VPVNP.Binary.full_rank_character
#print axioms VPVNP.Binary.full_rank_entry_character

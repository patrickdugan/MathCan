import CanonicalRankRecurrence

/-! VPVNP-02I: outer-product bijection and rank-one character counts. -/
open scoped BigOperators
open Finset
namespace VPVNP.Binary
noncomputable section

abbrev NZVec (n : ℕ) := {u : BinarySpace n // u ≠ 0}
abbrev RankOneMat (n : ℕ) := {W : BinMat (Fin n) // W.rank = 1}

local instance nzVecFintype (n : ℕ) : Fintype (NZVec n) := Fintype.ofFinite _
local instance rankOneFintype (n : ℕ) : Fintype (RankOneMat n) := Fintype.ofFinite _

theorem nzVec_card (n : ℕ) : Fintype.card (NZVec n) = 2^n-1 := by
  classical
  calc
    Fintype.card (NZVec n) = (univ.erase (0 : BinarySpace n)).card :=
      Fintype.card_of_subtype _ (fun x => by simp)
    _ = _ := by rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, binary_space_card]

theorem exists_one_coordinate {n : ℕ} (u : BinarySpace n) (hu : u ≠ 0) :
    ∃ i : Fin n, u i = 1 := by
  by_contra h
  apply hu
  funext i
  change u i = 0
  rcases bit_cases (u i) with hz | ho
  · exact hz
  · exact False.elim (h ⟨i,ho⟩)

theorem matrix_rank_zero_imp_zero {n : ℕ} (W : BinMat (Fin n)) (hr : W.rank = 0) :
    W=0 := by
  rw [Matrix.rank_eq_finrank_span_cols] at hr
  have hz := (finrank_zero_iff_forall_zero).1 hr
  ext i j
  let col : Submodule.span (ZMod 2) (Set.range W.col) :=
    ⟨W.col j, Submodule.subset_span ⟨j,rfl⟩⟩
  have h := congrArg Subtype.val (hz col)
  exact congrFun h i

theorem outer_rank_one {n : ℕ} (u v : NZVec n) :
    (Matrix.vecMulVec u.1 v.1).rank = 1 := by
  have hle := Matrix.rank_vecMulVec_le u.1 v.1
  have hne : (Matrix.vecMulVec u.1 v.1).rank ≠ 0 := by
    intro h
    exact Matrix.vecMulVec_ne_zero u.2 v.2 (matrix_rank_zero_imp_zero _ h)
  omega

/-- Nonzero factors are unique over F2: one entry pins both scales. -/
theorem outer_injective {n : ℕ} :
    Function.Injective (fun p : NZVec n × NZVec n => Matrix.vecMulVec p.1.1 p.2.1) := by
  rintro ⟨u,v⟩ ⟨u',v'⟩ h
  obtain ⟨i,hi⟩ := exists_one_coordinate u.1 u.2
  obtain ⟨j,hj⟩ := exists_one_coordinate v.1 v.2
  have hentry : u.1 i*v.1 j = u'.1 i*v'.1 j := congrFun (congrFun h i) j
  rw [hi,hj,one_mul] at hentry
  have hi' : u'.1 i = 1 := by
    rcases bit_cases (u'.1 i) with hz | ho
    · rw [hz,zero_mul] at hentry
      exact False.elim (one_ne_zero hentry)
    · exact ho
  have hj' : v'.1 j = 1 := by
    rw [hi',one_mul] at hentry
    exact hentry.symm
  apply Prod.ext
  · apply Subtype.ext
    funext t
    have he : u.1 t*v.1 j = u'.1 t*v'.1 j := congrFun (congrFun h t) j
    simpa only [hj,hj',mul_one] using he
  · apply Subtype.ext
    funext t
    have he : u.1 i*v.1 t = u'.1 i*v'.1 t := congrFun (congrFun h i) t
    simpa only [hi,hi',one_mul] using he

/-- A rank-one matrix has all its columns in the line of a nonzero column. -/
theorem outer_surjective {n : ℕ} (W : RankOneMat n) :
    ∃ p : NZVec n × NZVec n, Matrix.vecMulVec p.1.1 p.2.1 = W.1 := by
  classical
  have hn : W.1 ≠ 0 := by
    intro h
    have hr := W.2
    rw [h,Matrix.rank_zero] at hr
    omega
  have hentry : ∃ i j, W.1 i j ≠ 0 := by
    by_contra! h
    apply hn
    ext i j
    exact h i j
  obtain ⟨i,j,hij⟩ := hentry
  let S := Submodule.span (ZMod 2) (Set.range W.1.col)
  have hs : Module.finrank (ZMod 2) S = 1 := by
    simpa only [S, Matrix.rank_eq_finrank_span_cols] using W.2
  let u : S := ⟨W.1.col j, Submodule.subset_span ⟨j,rfl⟩⟩
  have hu : (u : BinarySpace n) ≠ 0 := by
    intro h
    exact hij (congrFun h i)
  have hu' : u ≠ 0 := by
    intro h
    exact hu (congrArg Subtype.val h)
  let col (t : Fin n) : S := ⟨W.1.col t, Submodule.subset_span ⟨t,rfl⟩⟩
  have hex : ∀ t, ∃ c : ZMod 2, c • u = col t :=
    fun t => exists_smul_eq_of_finrank_eq_one hs hu' (col t)
  choose v hv using hex
  have hmat : Matrix.vecMulVec (u : BinarySpace n) v = W.1 := by
    ext a b
    have he := congrFun (congrArg Subtype.val (hv b)) a
    change v b * (u : BinarySpace n) a = W.1 a b at he
    change (u : BinarySpace n) a * v b = W.1 a b
    rw [mul_comm]
    exact he
  have hv0 : v ≠ 0 := by
    intro h
    rw [h,Matrix.vecMulVec_zero] at hmat
    exact hn hmat.symm
  exact ⟨(⟨u.1,hu⟩,⟨v,hv0⟩),hmat⟩

def outerEquiv (n : ℕ) : NZVec n × NZVec n ≃ RankOneMat n :=
  Equiv.ofBijective
    (fun p => ⟨Matrix.vecMulVec p.1.1 p.2.1, outer_rank_one p.1 p.2⟩)
    ⟨fun _ _ h => outer_injective (congrArg Subtype.val h),
      fun W => by
        obtain ⟨p,hp⟩ := outer_surjective W
        exact ⟨p,Subtype.ext hp⟩⟩

theorem rank_one_card (n : ℕ) : Fintype.card (RankOneMat n) = (2^n-1)^2 := by
  rw [← Fintype.card_congr (outerEquiv n), Fintype.card_prod, nzVec_card, pow_two]

def matrixWalsh {n : ℕ} (B W : BinMat (Fin n)) : ℝ :=
  walsh (fun p : Fin n × Fin n => B p.1 p.2)
    (fun p : Fin n × Fin n => W p.1 p.2)

theorem outer_pairing {n : ℕ} (B : BinMat (Fin n)) (u v : BinarySpace n) :
    parityPair (fun p : Fin n × Fin n => B p.1 p.2)
      (fun p : Fin n × Fin n => Matrix.vecMulVec u v p.1 p.2) =
        parityPair (Matrix.mulVec B.transpose u) v := by
  unfold parityPair
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem outer_walsh {n : ℕ} (B : BinMat (Fin n)) (u v : BinarySpace n) :
    matrixWalsh B (Matrix.vecMulVec u v) = walsh (Matrix.mulVec B.transpose u) v := by
  unfold matrixWalsh walsh
  rw [outer_pairing]

theorem sum_nonzero_add {n : ℕ} (f : BinarySpace n → ℝ) :
    (∑ u : NZVec n, f u.1) + f 0 = ∑ u : BinarySpace n, f u := by
  classical
  rw [← Finset.sum_subtype (univ.erase (0 : BinarySpace n)) (fun x => by simp) f]
  exact Finset.sum_erase_add univ f (mem_univ _)

theorem walsh_at_zero {n : ℕ} (a : BinarySpace n) : walsh a 0 = 1 := by
  rw [walsh_symm]
  simp [walsh,bitSign,pairing_zero_left]

theorem walsh_full_sum {n : ℕ} (a : BinarySpace n) :
    (∑ v : BinarySpace n, walsh a v) = if a=0 then (2:ℝ)^n else 0 := by
  classical
  by_cases h : a=0
  · subst a
    rw [if_pos rfl,walsh_sum_at_zero,binary_space_card]
    norm_cast
  · rw [if_neg h,walsh_sum_zero _ h]

theorem kernel_dim {n : ℕ} (B : BinMat (Fin n)) :
    Module.finrank (ZMod 2) (LinearMap.ker B.transpose.mulVecLin) = n-B.rank := by
  have h := B.transpose.mulVecLin.finrank_range_add_finrank_ker
  change B.transpose.rank + Module.finrank (ZMod 2) (LinearMap.ker B.transpose.mulVecLin) =
    Module.finrank (ZMod 2) (Fin n → ZMod 2) at h
  rw [Matrix.rank_transpose,Module.finrank_fin_fun] at h
  omega

theorem kernel_vector_card {n : ℕ} (B : BinMat (Fin n)) :
    (univ.filter (fun u : BinarySpace n => Matrix.mulVec B.transpose u = 0)).card =
      2^(n-B.rank) := by
  classical
  let K := LinearMap.ker B.transpose.mulVecLin
  letI : Fintype K := Fintype.ofFinite _
  let e : K ≃ₗ[ZMod 2] BinarySpace (n-B.rank) :=
    LinearEquiv.ofFinrankEq K (BinarySpace (n-B.rank)) (by
      change Module.finrank (ZMod 2) (LinearMap.ker B.transpose.mulVecLin) =
        Module.finrank (ZMod 2) (Fin (n-B.rank) → ZMod 2)
      rw [kernel_dim,Module.finrank_fin_fun])
  calc
    _ = Fintype.card K := (Fintype.card_of_subtype _ (fun u => by
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      change Matrix.mulVec B.transpose u = 0 ↔ Matrix.mulVec B.transpose u = 0
      rfl)).symm
    _ = _ := (Fintype.card_congr e.toEquiv).trans (binary_space_card _)

theorem outer_full_sum {n : ℕ} (B : BinMat (Fin n)) :
    (∑ u : BinarySpace n, ∑ v : BinarySpace n, walsh (Matrix.mulVec B.transpose u) v) =
      (2:ℝ)^n * (2:ℝ)^(n-B.rank) := by
  classical
  simp_rw [walsh_full_sum]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, kernel_vector_card]
  push_cast
  ring

/-- Signed character count over the actual set of rank-one matrices. -/
theorem rank_one_signed {n : ℕ} (B : BinMat (Fin n)) :
    (∑ W : RankOneMat n, matrixWalsh B W.1) =
      (2:ℝ)^n * (2:ℝ)^(n-B.rank) - 2*(2:ℝ)^n+1 := by
  classical
  let f (u : BinarySpace n) := ∑ v : NZVec n, walsh (Matrix.mulVec B.transpose u) v.1
  have houter : (∑ W : RankOneMat n, matrixWalsh B W.1) = ∑ u : NZVec n, f u.1 := by
    calc
      _ = ∑ p : NZVec n × NZVec n, matrixWalsh B (Matrix.vecMulVec p.1.1 p.2.1) :=
        (Fintype.sum_equiv (outerEquiv n) _ _ (fun _ => rfl)).symm
      _ = _ := by rw [Fintype.sum_prod_type]; simp only [outer_walsh,f]
  have hinner (u : BinarySpace n) :
      (∑ v : BinarySpace n, walsh (Matrix.mulVec B.transpose u) v) = f u+1 := by
    simpa only [walsh_at_zero,f] using
      (sum_nonzero_add (fun v => walsh (Matrix.mulVec B.transpose u) v)).symm
  have hzero : f 0 = (2:ℝ)^n-1 := by
    have hh := hinner 0
    rw [Matrix.mulVec_zero,walsh_full_sum,if_pos rfl] at hh
    linarith
  have hall := outer_full_sum B
  simp_rw [hinner] at hall
  rw [Finset.sum_add_distrib] at hall
  have hc : (∑ _ : BinarySpace n, (1:ℝ)) = (2:ℝ)^n := by
    simp [binary_space_card]
  rw [hc, ← sum_nonzero_add f, hzero, ← houter] at hall
  linarith

def rankOneOddProb {n : ℕ} (B : BinMat (Fin n)) : ℝ :=
  (1-(∑ W : RankOneMat n, matrixWalsh B W.1) / Fintype.card (RankOneMat n))/2

theorem rank_one_odd_formula {n : ℕ} (hn : 0 < n) (B : BinMat (Fin n)) :
    rankOneOddProb B =
      (2:ℝ)^n * ((2:ℝ)^n-(2:ℝ)^(n-B.rank)) / (2*((2:ℝ)^n-1)^2) := by
  have hq : 1 < (2:ℝ)^n := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  have hqn : 1 ≤ (2:ℕ)^n := by have h : 0 < (2:ℕ)^n := pow_pos (by decide) _; omega
  have hne : (2:ℝ)^n-1 ≠ 0 := by linarith
  unfold rankOneOddProb
  rw [rank_one_signed,rank_one_card]
  push_cast [Nat.cast_sub hqn]
  field_simp [hne] <;> ring

end
end VPVNP.Binary

#print axioms VPVNP.Binary.nzVec_card
#print axioms VPVNP.Binary.matrix_rank_zero_imp_zero
#print axioms VPVNP.Binary.outer_rank_one
#print axioms VPVNP.Binary.outer_injective
#print axioms VPVNP.Binary.outer_surjective
#print axioms VPVNP.Binary.outerEquiv
#print axioms VPVNP.Binary.rank_one_card
#print axioms VPVNP.Binary.outer_pairing
#print axioms VPVNP.Binary.walsh_full_sum
#print axioms VPVNP.Binary.kernel_dim
#print axioms VPVNP.Binary.kernel_vector_card
#print axioms VPVNP.Binary.outer_full_sum
#print axioms VPVNP.Binary.rank_one_signed
#print axioms VPVNP.Binary.rank_one_odd_formula

import Mathlib

/-!
Independent finite-dimensional abstraction of the local multiplicity
capacity mechanism documented in RH26B08_RANK_CERTIFICATE.md.
The source's arithmetic and automorphic hypotheses are outside this module.
-/

namespace RH26E04A

open scoped BigOperators

section Counting

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def labels (I : Finset ι) (A : ι → Finset σ) : Finset σ :=
  I.biUnion A

def occurrences (I : Finset ι) (A : ι → Finset σ) (s : σ) : ℕ :=
  (I.filter fun i => s ∈ A i).card

def total (I : Finset ι) (A : ι → Finset σ) (d : σ → ℕ) : ℕ :=
  ∑ i ∈ I, ∑ s ∈ A i, d s

def overlapDefect (I : Finset ι) (A : ι → Finset σ) (d : σ → ℕ) : ℕ :=
  ∑ s ∈ labels I A, (occurrences I A s - 1) * d s

theorem occurrence_positive (I : Finset ι) (A : ι → Finset σ) (s : σ) :
    s ∈ labels I A ↔ 0 < occurrences I A s := by
  unfold labels occurrences
  constructor
  · intro hs
    obtain ⟨i, hi, hsi⟩ := Finset.mem_biUnion.mp hs
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hsi⟩⟩
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h
    obtain ⟨hiI, hsi⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_biUnion.mpr ⟨i, hiI, hsi⟩

/-- Exchange the order of a finite incidence sum. -/
theorem weighted_count (I : Finset ι) (A : ι → Finset σ) (d : σ → ℕ) :
    total I A d = ∑ s ∈ labels I A, occurrences I A s * d s := by
  unfold total
  calc
    _ = ∑ i ∈ I, ∑ s ∈ labels I A, if s ∈ A i then d s else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have he : (labels I A).filter (fun s => s ∈ A i) = A i := by
        ext s
        simp only [Finset.mem_filter]
        constructor
        · exact And.right
        · intro hs
          exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, hs⟩, hs⟩
      rw [← Finset.sum_filter, he]
    _ = ∑ s ∈ labels I A, ∑ i ∈ I, if s ∈ A i then d s else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rfl

/-- The exact extra charge for repeated labels, with natural-number weights. -/
theorem overlap_identity (I : Finset ι) (A : ι → Finset σ) (d : σ → ℕ) :
    total I A d = (∑ s ∈ labels I A, d s) + overlapDefect I A d := by
  rw [weighted_count]
  unfold overlapDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hp := (occurrence_positive I A s).mp hs
  have he : 1 + (occurrences I A s - 1) = occurrences I A s := by omega
  calc
    occurrences I A s * d s = (1 + (occurrences I A s - 1)) * d s := by rw [he]
    _ = d s + (occurrences I A s - 1) * d s := by rw [Nat.add_mul, one_mul]

/-- Unique localization of labels makes the duplicate defect vanish. -/
theorem overlap_zero_of_disjoint (I : Finset ι) (A : ι → Finset σ) (d : σ → ℕ)
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)) :
    overlapDefect I A d = 0 := by
  unfold overlapDefect
  apply Finset.sum_eq_zero
  intro s hs
  obtain ⟨i, hi, hsi⟩ := Finset.mem_biUnion.mp (show s ∈ I.biUnion A from hs)
  have he : I.filter (fun j => s ∈ A j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hn
      exact (Finset.disjoint_left.mp (hdis j hj.1 i hi hn)) hj.2 hsi
    · rintro rfl
      exact ⟨hi, hsi⟩
  simp [occurrences, he]

theorem budget_with_overlap (I : Finset ι) (A : ι → Finset σ)
    (d : σ → ℕ) (m : ι → ℕ) (R : ℕ)
    (hlocal : ∀ i ∈ I, m i ≤ ∑ s ∈ A i, d s)
    (hcapacity : (∑ s ∈ labels I A, d s) ≤ R) :
    (∑ i ∈ I, m i) ≤ R + overlapDefect I A d := by
  calc
    _ ≤ total I A d := Finset.sum_le_sum hlocal
    _ = _ := overlap_identity I A d
    _ ≤ _ := Nat.add_le_add_right hcapacity _

end Counting

section Subspaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Indexed independence certifies additivity of the selected subspace dimensions. -/
theorem independent_union_rank {σ : Type*} [DecidableEq σ]
    (U : σ → Submodule K V) (hU : iSupIndep U) (S : Finset σ) :
    (∑ s ∈ S, Module.finrank K (U s)) =
      Module.finrank K ↥(⨆ s ∈ S, U s) ∧
    (∑ s ∈ S, Module.finrank K (U s)) ≤ Module.finrank K V := by
  classical
  have hEq : (∑ s ∈ S, Module.finrank K (U s)) =
      Module.finrank K ↥(⨆ s ∈ S, U s) := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert s S hs ih =>
      let L : Submodule K V := ⨆ t ∈ S, U t
      have hsep : Disjoint (U s) L := hU.disjoint_biSup (by simpa using hs)
      have hjoin : (⨆ t ∈ insert s S, U t) = U s ⊔ L := by
        simp only [Finset.iSup_insert, L]
      have hadd : Module.finrank K (U s ⊔ L : Submodule K V) =
          Module.finrank K (U s) + Module.finrank K L := by
        have he := Submodule.finrank_sup_add_finrank_inf_eq (U s) L
        simpa [hsep.eq_bot] using he
      calc
        (∑ t ∈ insert s S, Module.finrank K (U t)) =
            Module.finrank K (U s) + Module.finrank K L := by
          rw [Finset.sum_insert hs, ih]
        _ = Module.finrank K (U s ⊔ L : Submodule K V) := hadd.symm
        _ = Module.finrank K ↥(⨆ t ∈ insert s S, U t) := by rw [hjoin]
  refine ⟨hEq, ?_⟩
  rw [hEq]
  exact Submodule.finrank_le _

theorem subspace_capacity {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (I : Finset ι) (A : ι → Finset σ) (U : σ → Submodule K V)
    (hU : iSupIndep U) (m : ι → ℕ)
    (hlocal : ∀ i ∈ I, m i ≤ ∑ s ∈ A i, Module.finrank K (U s)) :
    (∑ i ∈ I, m i) ≤ Module.finrank K V +
      overlapDefect I A (fun s => Module.finrank K (U s)) := by
  exact budget_with_overlap I A (fun s => Module.finrank K (U s)) m
    (Module.finrank K V) hlocal (independent_union_rank U hU (labels I A)).2

/-- Rank-nullity is a second, separate dimension defect for a certified map. -/
theorem rank_nullity_defect {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (F : W →ₗ[K] V) :
    Module.finrank K W = Module.finrank K (LinearMap.range F) +
      Module.finrank K (LinearMap.ker F) :=
  (LinearMap.finrank_range_add_finrank_ker F).symm

end Subspaces

def fixtureSets (i : Fin 2) : Finset (Fin 3) :=
  if i = 0 then {0, 1} else {1, 2}

theorem duplicate_label_fixture :
    let I : Finset (Fin 2) := Finset.univ
    let d : Fin 3 → ℕ := fun _ => 1
    total I fixtureSets d = 4 ∧
    (∑ s ∈ labels I fixtureSets, d s) = 3 ∧
    overlapDefect I fixtureSets d = 1 ∧
    (∑ s ∈ labels I fixtureSets, d s) < total I fixtureSets d ∧
    total I fixtureSets d =
      (∑ s ∈ labels I fixtureSets, d s) + overlapDefect I fixtureSets d := by
  decide

def firstLine : Fin 2 → ℚ := fun i => if i = 0 then 1 else 0
def secondLine : Fin 2 → ℚ := fun i => if i = 0 then 0 else 1
def diagonalLine : Fin 2 → ℚ := fun _ => 1

/-- Explicit two-vector linear independence, expressed as the zero relation test. -/
def PairFree (u v : Fin 2 → ℚ) : Prop :=
  ∀ a b : ℚ, a • u + b • v = 0 → a = 0 ∧ b = 0

theorem dependent_lines_control :
    firstLine ≠ 0 ∧ secondLine ≠ 0 ∧ diagonalLine ≠ 0 ∧
    PairFree firstLine secondLine ∧ PairFree firstLine diagonalLine ∧
    PairFree secondLine diagonalLine ∧
    (∃ a b c : ℚ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      a • firstLine + b • secondLine + c • diagonalLine = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have he := congrFun h (0 : Fin 2)
    norm_num [firstLine] at he
  · intro h
    have he := congrFun h (1 : Fin 2)
    norm_num [secondLine] at he
  · intro h
    have he := congrFun h (0 : Fin 2)
    norm_num [diagonalLine] at he
  · intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    norm_num [firstLine, secondLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
    exact ⟨h0, h1⟩
  · intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    norm_num [firstLine, diagonalLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
    exact ⟨by linarith, h1⟩
  · intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    norm_num [secondLine, diagonalLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
    exact ⟨by linarith, h0⟩
  · refine ⟨1, 1, -1, by norm_num, ?_⟩
    funext i
    fin_cases i <;>
      norm_num [firstLine, secondLine, diagonalLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end RH26E04A

#print axioms RH26E04A.occurrence_positive
#print axioms RH26E04A.weighted_count
#print axioms RH26E04A.overlap_identity
#print axioms RH26E04A.overlap_zero_of_disjoint
#print axioms RH26E04A.budget_with_overlap
#print axioms RH26E04A.independent_union_rank
#print axioms RH26E04A.subspace_capacity
#print axioms RH26E04A.rank_nullity_defect
#print axioms RH26E04A.duplicate_label_fixture
#print axioms RH26E04A.dependent_lines_control

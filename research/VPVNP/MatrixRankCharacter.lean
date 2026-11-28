import SignedFrameTransport

/-!
VPVNP-02G: actual GL character sums are invariant under two-sided
invertible transformations and hence depend only on matrix rank.
-/

open scoped BigOperators
open Finset
namespace VPVNP.Binary

noncomputable section

abbrev BinMat (I : Type*) := Matrix I I (ZMod 2)
abbrev MatUnits (I : Type*) [Fintype I] [DecidableEq I] := (BinMat I)ˣ

local instance unitMatrixFintype (I : Type*) [Fintype I] [DecidableEq I] :
    Fintype (MatUnits I) := by
  letI : Finite (MatUnits I) :=
    Finite.of_injective (fun w : MatUnits I => (w : BinMat I)) (by
      intro x y h
      exact Units.ext h)
  exact Fintype.ofFinite _

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def traceCharacter (B W : BinMat I) : ℝ :=
  bitSign (Matrix.trace (B * W))

def traceAverage (B : BinMat I) : ℝ :=
  (∑ W : MatUnits I, traceCharacter B (W : BinMat I)) / Fintype.card (MatUnits I)

theorem trace_character_cycle (B : BinMat I) (U V W : BinMat I) :
    traceCharacter (U * B * V) W = traceCharacter B (V * W * U) := by
  unfold traceCharacter
  congr 1
  calc
    Matrix.trace (U * B * V * W) = Matrix.trace (U * (B * V * W)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((B * V * W) * U) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (B * (V * W * U)) := by simp only [Matrix.mul_assoc]

/-- Uniform multiplication by units preserves the signed average. -/
theorem trace_average_mul_units (B : BinMat I) (U V : MatUnits I) :
    traceAverage ((U : BinMat I) * B * (V : BinMat I)) = traceAverage B := by
  unfold traceAverage
  congr 1
  let e : MatUnits I ≃ MatUnits I := (Equiv.mulLeft V).trans (Equiv.mulRight U)
  apply Fintype.sum_equiv e
  intro W
  change traceCharacter ((U : BinMat I) * B * (V : BinMat I)) (W : BinMat I) =
    traceCharacter B ((V : BinMat I) * (W : BinMat I) * (U : BinMat I))
  exact trace_character_cycle B U V W

theorem trace_reindex (e : I ≃ J) (A : BinMat I) :
    Matrix.trace (Matrix.reindexRingEquiv (ZMod 2) e A) = Matrix.trace A := by
  unfold Matrix.trace
  apply Fintype.sum_equiv e.symm
  intro j
  rfl

theorem trace_character_reindex (e : I ≃ J) (B W : BinMat I) :
    traceCharacter (Matrix.reindexRingEquiv (ZMod 2) e B)
      (Matrix.reindexRingEquiv (ZMod 2) e W) = traceCharacter B W := by
  unfold traceCharacter
  rw [← map_mul, trace_reindex]

/-- Simultaneous reindexing transports the entire uniform GL law. -/
theorem trace_average_reindex (e : I ≃ J) (B : BinMat I) :
    traceAverage (Matrix.reindexRingEquiv (ZMod 2) e B) = traceAverage B := by
  let r := Matrix.reindexRingEquiv (ZMod 2) e
  let u := Units.mapEquiv r.toMulEquiv
  unfold traceAverage
  have hcard : Fintype.card (MatUnits I) = Fintype.card (MatUnits J) :=
    Fintype.card_congr u.toEquiv
  rw [← hcard]
  congr 1
  symm
  apply Fintype.sum_equiv u.toEquiv
  intro W
  change traceCharacter B (W : BinMat I) =
    traceCharacter (r B) (r (W : BinMat I))
  exact (trace_character_reindex e B W).symm

def rankBlock (k d : ℕ) : BinMat (Fin k ⊕ Fin d) :=
  Matrix.fromBlocks 1 0 0 0

/-- Actual character average of a coefficient matrix equals that of its
identity/zero rank normal form. The finite field is fixed at F2. -/
theorem trace_average_rank_block (B : BinMat I) :
    traceAverage B = traceAverage (rankBlock B.rank (Fintype.card I - B.rank)) := by
  classical
  obtain ⟨V,U,e,hV,hU,h⟩ := Matrix.exists_rank_normal_form B
  rcases hV with ⟨v,rfl⟩
  rcases hU with ⟨u,rfl⟩
  have hn : Matrix.reindexRingEquiv (ZMod 2) e
      ((v : BinMat I) * B * (u : BinMat I)) =
        rankBlock B.rank (Fintype.card I - B.rank) := by
    rw [h]
    ext i j
    change (rankBlock B.rank (Fintype.card I - B.rank))
      (e (e.symm i)) (e (e.symm j)) = _
    simp
  calc
    traceAverage B = traceAverage ((v : BinMat I) * B * (u : BinMat I)) :=
      (trace_average_mul_units B v u).symm
    _ = traceAverage (Matrix.reindexRingEquiv (ZMod 2) e
          ((v : BinMat I) * B * (u : BinMat I))) :=
      (trace_average_reindex e _).symm
    _ = _ := by rw [hn]

theorem trace_average_rank_invariant (B C : BinMat I) (h : B.rank = C.rank) :
    traceAverage B = traceAverage C := by
  rw [trace_average_rank_block B, trace_average_rank_block C, h]

/-- Coordinate pairing used in BinaryWalsh equals trace of B-transpose times W. -/
theorem entry_pairing_trace (B W : BinMat I) :
    parityPair (fun p : I × I => B p.1 p.2) (fun p : I × I => W p.1 p.2) =
      Matrix.trace (B.transpose * W) := by
  unfold parityPair Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

def entryAverage (B : BinMat I) : ℝ :=
  (∑ W : MatUnits I, walsh (fun p : I × I => B p.1 p.2)
      (fun p : I × I => (W : BinMat I) p.1 p.2)) / Fintype.card (MatUnits I)

theorem entry_average_trace (B : BinMat I) :
    entryAverage B = traceAverage B.transpose := by
  unfold entryAverage traceAverage
  congr 1
  apply Finset.sum_congr rfl
  intro W hW
  unfold walsh traceCharacter
  rw [entry_pairing_trace]

/-- All dual coefficient matrices of the same rank have the same
full-rank increment character expectation, in the actual Walsh convention. -/
theorem entry_average_rank_invariant (B C : BinMat I) (h : B.rank = C.rank) :
    entryAverage B = entryAverage C := by
  rw [entry_average_trace, entry_average_trace]
  apply trace_average_rank_invariant
  simpa only [Matrix.rank_transpose] using h

end
end VPVNP.Binary

#print axioms VPVNP.Binary.trace_character_cycle
#print axioms VPVNP.Binary.trace_average_mul_units
#print axioms VPVNP.Binary.trace_reindex
#print axioms VPVNP.Binary.trace_character_reindex
#print axioms VPVNP.Binary.trace_average_reindex
#print axioms VPVNP.Binary.trace_average_rank_block
#print axioms VPVNP.Binary.trace_average_rank_invariant
#print axioms VPVNP.Binary.entry_pairing_trace
#print axioms VPVNP.Binary.entry_average_trace
#print axioms VPVNP.Binary.entry_average_rank_invariant

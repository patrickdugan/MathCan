import Mathlib

/-! BGS-01: exact black-box query obstruction and exponential Boolean
witness-union rank. No asymptotic P vs NP statement is asserted. -/
open scoped BigOperators Matrix Kronecker
namespace VPVNP.BGS

inductive QueryTree (ι : Type*) where
  | halt : Bool → QueryTree ι
  | ask : ι → QueryTree ι → QueryTree ι → QueryTree ι

namespace QueryTree
variable {ι : Type*}

def eval (o : ι → Bool) : QueryTree ι → Bool
  | halt b => b
  | ask i no yes => if o i then eval o yes else eval o no

def zeroPath : QueryTree ι → List ι
  | halt _ => []
  | ask i no _ => i :: zeroPath no

theorem eval_agree_zeroPath (t : QueryTree ι) (o : ι → Bool)
    (h : ∀ i ∈ t.zeroPath, o i = false) :
    t.eval o = t.eval (fun _ => false) := by
  induction t with
  | halt b => rfl
  | ask i no yes ihNo ihYes =>
    have hi := h i (by simp [zeroPath])
    have hn : ∀ j ∈ no.zeroPath, o j = false := fun j hj =>
      h j (by simp [zeroPath, hj])
    simpa [eval, hi] using ihNo hn

def oneHot [DecidableEq ι] (j : ι) (i : ι) : Bool := decide (i = j)

/-- Correctness on just the all-zero and one-hot oracles forces every
    possible witness to occur on the all-zero execution path. -/
theorem every_witness_on_zeroPath [DecidableEq ι] (t : QueryTree ι)
    (h0 : t.eval (fun _ => false) = false)
    (h1 : ∀ j, t.eval (oneHot j) = true) :
    ∀ j, j ∈ t.zeroPath := by
  intro j
  by_contra hj
  have h : ∀ i ∈ t.zeroPath, oneHot j i = false := by
    intro i hi
    have hne : i ≠ j := fun e => hj (e ▸ hi)
    simp [oneHot, hne]
  have he := eval_agree_zeroPath t (oneHot j) h
  rw [h1 j, h0] at he
  contradiction

theorem black_box_or_query_bound [Fintype ι] [DecidableEq ι] (t : QueryTree ι)
    (h : ∀ o : ι → Bool, t.eval o = true ↔ ∃ i, o i = true) :
    Fintype.card ι ≤ t.zeroPath.length := by
  have h0 : t.eval (fun _ => false) = false := by
    cases he : t.eval (fun _ => false) with
    | false => rfl
    | true =>
      obtain ⟨i, hi⟩ := (h _).mp he
      contradiction
  have h1 : ∀ j, t.eval (oneHot j) = true := fun j =>
    (h _).mpr ⟨j, by simp [oneHot]⟩
  have hall := every_witness_on_zeroPath t h0 h1
  have hs : (Finset.univ : Finset ι) ⊆ t.zeroPath.toFinset := by
    intro i _
    simpa using hall i
  exact (by simpa using Finset.card_le_card hs : Fintype.card ι ≤ t.zeroPath.toFinset.card).trans
    (List.toFinset_card_le _)

theorem nbit_or_query_bound (n : ℕ) (t : QueryTree (Fin n → Bool))
    (h : ∀ o : (Fin n → Bool) → Bool, t.eval o = true ↔ ∃ i, o i = true) :
    2^n ≤ t.zeroPath.length := by
  simpa [Fintype.card_fun] using black_box_or_query_bound t h

end QueryTree

section MatrixRanks

variable (K : Type*) [Field K]

/-- Finite bit strings, grouped by their first bit. -/
def Cube : ℕ → Type
  | 0 => Unit
  | n+1 => Fin 2 × Cube n

instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := cubeFintype n
           inferInstanceAs (Fintype (Fin 2 × Cube n))

instance cubeDecEq : (n : ℕ) → DecidableEq (Cube n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 => letI := cubeDecEq n
           inferInstanceAs (DecidableEq (Fin 2 × Cube n))

def zeroCube : (n : ℕ) → Cube n
  | 0 => ()
  | n+1 => (0,zeroCube n)

theorem cube_card (n : ℕ) : Fintype.card (Cube n) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Fin 2 × Cube n) = 2^(n+1)
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ, Nat.mul_comm]

def bitD : Matrix (Fin 2) (Fin 2) K := !![1,1;1,0]
def bitInv : Matrix (Fin 2) (Fin 2) K := !![0,1;1,-1]

theorem bitD_inv : bitD K * bitInv K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitD, bitInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Disjointness is the product of the one-bit disjointness tables. -/
def disjoint : (n : ℕ) → Matrix (Cube n) (Cube n) K
  | 0 => 1
  | n+1 => bitD K ⊗ₖ disjoint n

def disjointInv : (n : ℕ) → Matrix (Cube n) (Cube n) K
  | 0 => 1
  | n+1 => bitInv K ⊗ₖ disjointInv n

theorem disjoint_inv (n : ℕ) : disjoint K n * disjointInv K n = 1 := by
  induction n with
  | zero => simp [disjoint, disjointInv]
  | succ n ih =>
    change (bitD K ⊗ₖ disjoint K n) * (bitInv K ⊗ₖ disjointInv K n) = 1
    rw [← Matrix.mul_kronecker_mul, bitD_inv, ih, Matrix.one_kronecker_one]

theorem disjoint_rank (n : ℕ) : (disjoint K n).rank = 2^n := by
  have h := Matrix.rank_mul_le_left (disjoint K n) (disjointInv K n)
  rw [disjoint_inv, Matrix.rank_one, cube_card] at h
  exact le_antisymm (by simpa [cube_card] using (disjoint K n).rank_le_card_width) h

theorem disjoint_zero_col (n : ℕ) (x : Cube n) :
    disjoint K n x (zeroCube n) = 1 := by
  induction n with
  | zero =>
    cases x
    simp [disjoint, zeroCube, Matrix.one_apply]
  | succ n ih =>
    change (bitD K ⊗ₖ disjoint K n) x (0,zeroCube n) = 1
    obtain ⟨i,a⟩ := x
    rw [Matrix.kronecker_apply, ih a, mul_one]
    fin_cases i <;> simp [bitD]

theorem disjoint_zero_row (n : ℕ) (y : Cube n) :
    disjoint K n (zeroCube n) y = 1 := by
  induction n with
  | zero =>
    cases y
    simp [disjoint, zeroCube, Matrix.one_apply]
  | succ n ih =>
    change (bitD K ⊗ₖ disjoint K n) (0,zeroCube n) y = 1
    obtain ⟨j,b⟩ := y
    rw [Matrix.kronecker_apply, ih b, mul_one]
    fin_cases j <;> simp [bitD]

/-- An invertible matrix with an all-one row and column at z has a
    rank-(N-1) entrywise complement.  It is D*(E-I), with E sending
    every column to the z basis vector. -/
theorem complement_rank {I : Type*} [Fintype I] [DecidableEq I]
    (D : Matrix I I K) (z : I)
    (hD : D.rank = Fintype.card I)
    (hcol : ∀ i, D i z = 1) (hrow : ∀ j, D z j = 1) :
    (Matrix.of fun i j => 1-D i j).rank = Fintype.card I - 1 := by
  classical
  let E : Matrix I I K := Matrix.of fun i _ => if i = z then 1 else 0
  let P : Matrix I I K := E - 1
  let N : Matrix I I K := Matrix.of fun i j => 1-D i j
  let S : Finset I := Finset.univ.erase z
  have hDE : D * E = Matrix.of (fun (_ _ : I) => (1:K)) := by
    ext i j
    simp [Matrix.mul_apply, E, mul_ite, hcol]
  have hNP : D * P = N := by
    rw [show P = E-1 from rfl, Matrix.mul_sub, hDE, Matrix.mul_one]
    rfl
  have hsmall : P.submatrix (fun i : S => i.val) (fun j : S => j.val) =
      -(1 : Matrix S S K) := by
    ext i j
    have hi : i.val ≠ z := (Finset.mem_erase.mp i.property).1
    have he : (i.val = j.val) ↔ i = j := Subtype.ext_iff.symm
    simp [P, E, hi, Matrix.one_apply, he]
  have hneg : (-(1 : Matrix S S K)).rank = Fintype.card S := by
    have h := Matrix.rank_mul_le_left (-(1 : Matrix S S K)) (-(1 : Matrix S S K))
    rw [neg_mul_neg, Matrix.one_mul, Matrix.rank_one] at h
    exact le_antisymm (Matrix.rank_le_card_width _) h
  have hp : Fintype.card S ≤ P.rank := by
    have h := Matrix.rank_submatrix_le P (fun i : S => i.val) (fun j : S => j.val)
    rw [hsmall, hneg] at h
    exact h
  have hs : S.card = Fintype.card I - 1 := by
    simp [S, Finset.card_erase_of_mem (Finset.mem_univ z)]
  have hs' : Fintype.card S = Fintype.card I - 1 := by simpa using hs
  have hprod := Matrix.rank_mul_ge D P
  rw [hD, hNP] at hprod
  have hlo : Fintype.card I - 1 ≤ N.rank := by omega
  have hu : N.rank ≤ S.card := by
    apply Matrix.rank_le_card_of_support_subset
    intro i hi
    have hine : i ≠ z := by
      intro e
      subst i
      apply hi
      funext j
      simp [N, Matrix.row, hrow]
    exact Finset.mem_erase.mpr ⟨hine, Finset.mem_univ _⟩
  change N.rank = _
  exact le_antisymm (hu.trans_eq hs) hlo

theorem nondisjoint_rank (n : ℕ) :
    (Matrix.of fun (x y : Cube n) => 1-disjoint K n x y).rank = 2^n-1 := by
  have h := complement_rank K (disjoint K n) (zeroCube n)
    (by rw [disjoint_rank, cube_card]) (disjoint_zero_col K n) (disjoint_zero_row K n)
  rwa [cube_card] at h

end MatrixRanks
end VPVNP.BGS

#print axioms VPVNP.BGS.QueryTree.eval_agree_zeroPath
#print axioms VPVNP.BGS.QueryTree.every_witness_on_zeroPath
#print axioms VPVNP.BGS.QueryTree.black_box_or_query_bound
#print axioms VPVNP.BGS.QueryTree.nbit_or_query_bound
#print axioms VPVNP.BGS.cube_card
#print axioms VPVNP.BGS.bitD_inv
#print axioms VPVNP.BGS.disjoint_inv
#print axioms VPVNP.BGS.disjoint_rank
#print axioms VPVNP.BGS.disjoint_zero_col
#print axioms VPVNP.BGS.disjoint_zero_row
#print axioms VPVNP.BGS.complement_rank
#print axioms VPVNP.BGS.nondisjoint_rank

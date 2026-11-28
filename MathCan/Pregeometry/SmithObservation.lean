import Std

/-!
# Observation fibers under certified integer basis reductions

The abstract reduction theorem works for arbitrary phase representations,
provided the supplied row and column maps have certified inverses and the
observation diagram commutes. A Smith normal form reduction supplies such
maps after reduction modulo any M, or on the real phase torus.

No existence theorem for Smith normal form, or general gcd-count theorem,
is assumed by the finite Lean checks below.
-/

namespace MathCan.Pregeometry.SmithObservation

structure Reduction (X X' Y Y' : Type) where
  observe : X → Y
  diagonal : X' → Y'
  cols : X → X'
  colsInv : X' → X
  rows : Y → Y'
  rowsInv : Y' → Y
  col_left : ∀ x, colsInv (cols x) = x
  col_right : ∀ x, cols (colsInv x) = x
  row_left : ∀ y, rowsInv (rows y) = y
  intertwine : ∀ x, rows (observe x) = diagonal (cols x)

variable {X X' Y Y' : Type}

theorem fiber_iff (R : Reduction X X' Y Y') (x : X) (y : Y) :
    R.observe x = y ↔ R.diagonal (R.cols x) = R.rows y := by
  constructor
  · intro h
    exact (R.intertwine x).symm.trans (congrArg R.rows h)
  · intro h
    have h' := congrArg R.rowsInv ((R.intertwine x).trans h)
    simpa only [R.row_left] using h'

def fiberForward (R : Reduction X X' Y Y') (y : Y)
    (x : {x : X // R.observe x = y}) :
    {x : X' // R.diagonal x = R.rows y} :=
  ⟨R.cols x.val, (fiber_iff R x.val y).mp x.property⟩

def fiberBackward (R : Reduction X X' Y Y') (y : Y)
    (x : {x : X' // R.diagonal x = R.rows y}) :
    {x : X // R.observe x = y} :=
  ⟨R.colsInv x.val, (fiber_iff R (R.colsInv x.val) y).mpr (by
    rw [R.col_right]
    exact x.property)⟩

theorem fiber_backward_forward (R : Reduction X X' Y Y') (y : Y)
    (x : {x : X // R.observe x = y}) :
    fiberBackward R y (fiberForward R y x) = x := by
  apply Subtype.ext
  exact R.col_left x.val

theorem fiber_forward_backward (R : Reduction X X' Y Y') (y : Y)
    (x : {x : X' // R.diagonal x = R.rows y}) :
    fiberForward R y (fiberBackward R y x) = x := by
  apply Subtype.ext
  exact R.col_right x.val

/-- Integer row and column transformations for [[2,4],[6,8]] -> diag(2,4). -/
theorem mixed_reduction_intertwines (x y : Int) :
    2*x + 4*y = 2*(x + 2*y) ∧
    3*(2*x + 4*y) - (6*x + 8*y) = 4*y := by
  constructor <;> omega

theorem mixed_row_inverse (x y : Int) : 3*x - (3*x - y) = y := by omega

theorem mixed_column_inverse (x y : Int) :
    x + 2*y - 2*y = x ∧ x - 2*y + 2*y = x := by
  constructor <;> omega

def kernelCount2 (m a b c d : Nat) : Nat :=
  ((List.range m).flatMap (fun x =>
    (List.range m).filter (fun y =>
      (a*x+b*y)%m == 0 && (c*x+d*y)%m == 0))).length

def moduli : List Nat := [2,3,4,5,6,8,12]

theorem mixed_kernel_counts :
    moduli.map (fun m => kernelCount2 m 2 4 6 8) = [4,1,8,1,4,8,8] := by
  decide +kernel

theorem diagonal_kernel_counts :
    moduli.map (fun m => kernelCount2 m 2 0 0 4) = [4,1,8,1,4,8,8] := by
  decide +kernel

theorem mixed_matches_diagonal_on_fixture_moduli :
    moduli.map (fun m => kernelCount2 m 2 4 6 8) =
    moduli.map (fun m => kernelCount2 m 2 0 0 4) := by
  rw [mixed_kernel_counts, diagonal_kernel_counts]

#print axioms fiber_iff
#print axioms fiber_backward_forward
#print axioms fiber_forward_backward
#print axioms mixed_reduction_intertwines
#print axioms mixed_kernel_counts
#print axioms mixed_matches_diagonal_on_fixture_moduli

/-! ## BPD-QPU03: an exact finite alias chain on Z/8^3 -/

def phaseShiftGrid : List (List Nat) :=
  (List.range 8).flatMap (fun a =>
    (List.range 8).flatMap (fun b =>
      (List.range 8).map (fun c => [a,b,c])))

def phaseKernel (rows : List (List Nat)) : List (List Nat) :=
  phaseShiftGrid.filter (fun x =>
    rows.all (fun r =>
      (r.getD 0 0 * x.getD 0 0 + r.getD 1 0 * x.getD 1 0 +
        r.getD 2 0 * x.getD 2 0) % 8 == 0))

def evenRows : List (List Nat) := [[2,0,0],[0,2,0],[0,0,2]]
def pairRows : List (List Nat) := [[1,1,0],[0,1,1],[1,0,1]]

set_option maxRecDepth 10000 in
theorem even_scout_eight_aliases :
    phaseKernel evenRows =
      [[0,0,0],[0,0,4],[0,4,0],[0,4,4],
       [4,0,0],[4,0,4],[4,4,0],[4,4,4]] := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem pair_sums_leave_global_alias :
    phaseKernel (evenRows ++ pairRows) = [[0,0,0],[4,4,4]] := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem odd_triple_removes_global_alias :
    phaseKernel (evenRows ++ pairRows ++ [[1,1,1]]) = [[0,0,0]] := by
  decide +kernel

#print axioms even_scout_eight_aliases
#print axioms pair_sums_leave_global_alias
#print axioms odd_triple_removes_global_alias

end MathCan.Pregeometry.SmithObservation

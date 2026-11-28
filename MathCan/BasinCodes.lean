import Init

/-!
NOR-08: finite basin-label capacity lower bound.

If hidden states x_i lie near distinct attractor anchors p_i and a
representation assigns the same terminal code to x_i and x_j, its
additive distance-error budget must accommodate their anchor distance
up to both tail radii. A finite-distortion encoder therefore injects
on all sufficiently separated basin labels.

The proof uses an abstract Nat-valued triangle inequality and omega.
It does not assume pretrained model semantics or external analytic results.
-/
namespace MathCan.BasinCodes

/-- Two encoded terminal states with the same code need error
at least center distance minus their two terminal radii. -/
theorem shared_code_forces_separation_budget
    {Index State Code : Type}
    (d : State → State → Nat)
    (tri : ∀ u v w, d u w ≤ d u v + d v w)
    (anchor terminal : Index → State)
    (code : Index → Code)
    (radius : Index → Nat)
    (error : Nat)
    (nearLeft : ∀ i, d (anchor i) (terminal i) ≤ radius i)
    (nearRight : ∀ i, d (terminal i) (anchor i) ≤ radius i)
    (sameCode : ∀ i j, code i = code j →
      d (terminal i) (terminal j) ≤ error)
    (i j : Index) (hCode : code i = code j) :
    d (anchor i) (anchor j) ≤ radius i + radius j + error := by
  have h1 := tri (anchor i) (terminal i) (anchor j)
  have h2 := tri (terminal i) (terminal j) (anchor j)
  have hrad1 := nearLeft i
  have hrad2 := nearRight j
  have he := sameCode i j hCode
  omega

/-- Any additive-distortion terminal representation must assign
different codes to basins with pairwise separation exceeding both
tail radii plus the allowed error. -/
theorem separated_basins_require_injective_codes
    {Index State Code : Type}
    (d : State → State → Nat)
    (tri : ∀ u v w, d u w ≤ d u v + d v w)
    (anchor terminal : Index → State)
    (code : Index → Code)
    (radius : Index → Nat)
    (error : Nat)
    (nearLeft : ∀ i, d (anchor i) (terminal i) ≤ radius i)
    (nearRight : ∀ i, d (terminal i) (anchor i) ≤ radius i)
    (sameCode : ∀ i j, code i = code j →
      d (terminal i) (terminal j) ≤ error)
    (separated : ∀ i j, i ≠ j →
      radius i + radius j + error < d (anchor i) (anchor j)) :
    Function.Injective code := by
  intro i j hcode
  by_cases hij : i = j
  · exact hij
  · have hbound :=
      shared_code_forces_separation_budget
        d tri anchor terminal code radius error
        nearLeft nearRight sameCode i j hcode
    have hsep := separated i j hij
    omega

/-- A finite-level incompatibility witness: identifying two different
source basins violates their strict metric-separation margin. -/
theorem strict_margin_refutes_code_collision
    {Index State Code : Type}
    (d : State → State → Nat)
    (tri : ∀ u v w, d u w ≤ d u v + d v w)
    (anchor terminal : Index → State) (code : Index → Code)
    (radius : Index → Nat) (error : Nat)
    (nearLeft : ∀ i, d (anchor i) (terminal i) ≤ radius i)
    (nearRight : ∀ i, d (terminal i) (anchor i) ≤ radius i)
    (sameCode : ∀ i j, code i = code j →
      d (terminal i) (terminal j) ≤ error)
    (i j : Index)
    (hsep : radius i + radius j + error < d (anchor i) (anchor j)) :
    code i ≠ code j := by
  intro h
  have hbound :=
    shared_code_forces_separation_budget
      d tri anchor terminal code radius error
      nearLeft nearRight sameCode i j h
  omega

#print axioms shared_code_forces_separation_budget
#print axioms separated_basins_require_injective_codes
#print axioms strict_margin_refutes_code_collision

end MathCan.BasinCodes

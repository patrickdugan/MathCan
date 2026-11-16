import MathCan.TaylorPolynomial

/-! Concrete axis Taylor matrices, polynomial meaning, integrality and explicit
finite row budgets. These identities cover finite jets; analytic remainder
estimates for non-polynomial smooth functions are separate obligations. -/
namespace MathCan.TaylorTransport
open Std Lean.Grind MathCan.TaylorPolynomial
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast Ring.intCast

def compatible {d : Nat} (axis : Fin d) (beta gamma : Fin d → Nat) : Prop :=
  ∀ j, j≠axis → gamma j=beta j

instance compatibleDecidable {d : Nat} (axis : Fin d) (beta gamma : Fin d → Nat) :
    Decidable (compatible axis beta gamma) := by
  unfold compatible
  infer_instance

def entry {d : Nat} (axis : Fin d) (h : R) (beta gamma : Fin d → Nat) : R :=
  if compatible axis beta gamma ∧ beta axis≤gamma axis then
    (choose (gamma axis) (beta axis):R)*h^(gamma axis-beta axis) else 0

def entryInt {d : Nat} (axis : Fin d) (h : Int) (beta gamma : Fin d → Nat) : Int :=
  if compatible axis beta gamma ∧ beta axis≤gamma axis then
    (choose (gamma axis) (beta axis):Int)*h^(gamma axis-beta axis) else 0

theorem entry_integer {d : Nat} (axis : Fin d) (h : Int) (beta gamma : Fin d → Nat) :
    entry axis (h:R) beta gamma=(entryInt axis h beta gamma:R) := by
  unfold entry entryInt
  split <;> simp [Ring.intCast_zero,Ring.intCast_mul,Ring.intCast_natCast,Ring.intCast_pow]

theorem entry_self {d : Nat} (axis : Fin d) (h : R) (beta : Fin d → Nat) :
    entry axis h beta beta=1 := by
  have hc:compatible axis beta beta := by intro j _; rfl
  simp [entry,hc,choose_diagonal,Semiring.natCast_one,Semiring.pow_zero,Semiring.one_mul]

theorem entry_other_axis_zero {d : Nat} (axis j : Fin d) (h : R)
    (beta gamma : Fin d → Nat) (hj:j≠axis) (hne:gamma j≠beta j) : entry axis h beta gamma=0 := by
  have hc:¬compatible axis beta gamma := fun h=>hne (h j hj)
  simp [entry,hc]

theorem entry_lower_zero {d : Nat} (axis : Fin d) (h : R)
    (beta gamma : Fin d → Nat) (hbelow:gamma axis<beta axis) : entry axis h beta gamma=0 := by
  simp [entry,show ¬beta axis≤gamma axis by omega]

def transport {d J : Nat} (indices : Fin J → Fin d → Nat) (axis : Fin d)
    (h : R) (v : Fin J → R) (beta : Fin J) : R :=
  total (List.ofFn (fun gamma=>entry axis h (indices beta) (indices gamma)*v gamma))

def fibreTerms {d J : Nat} (indices : Fin J → Fin d → Nat) (axis : Fin d)
    (v : Fin J → R) (beta : Fin J) : List (Nat × R) :=
  List.ofFn (fun gamma=>(indices gamma axis,
    if compatible axis (indices beta) (indices gamma) then v gamma else 0))

/-- Each output jet coordinate is the normalized coefficient after affine
substitution in the exact polynomial fibre through that coordinate. -/
theorem transport_polynomial_coefficient {d J : Nat} (indices : Fin J → Fin d → Nat)
    (axis : Fin d) (h : R) (v : Fin J → R) (beta : Fin J) :
    coefficient (shiftTerms h (fibreTerms indices axis v beta)) (indices beta axis) =
      transport indices axis h v beta := by
  rw [shift_terms_coefficient]
  unfold translatedCoefficient fibreTerms transport
  rw [List.map_ofFn]
  apply congrArg total
  apply congrArg List.ofFn
  funext gamma
  by_cases hc:compatible axis (indices beta) (indices gamma)
  · by_cases hle:indices beta axis≤indices gamma axis
    · simp [entry,hc,hle]
    · have hz:=choose_above (indices gamma axis) (indices beta axis) (by omega)
      simp [entry,hc,hle,hz,Semiring.natCast_zero,Semiring.zero_mul]
  · simp [entry,hc,Semiring.mul_zero,Semiring.zero_mul]

theorem transport_polynomial_evaluate {d J : Nat} (indices : Fin J → Fin d → Nat)
    (axis : Fin d) (h x : R) (v : Fin J → R) (beta : Fin J) :
    evaluate (shiftTerms h (fibreTerms indices axis v beta)) x =
      evaluateTerms (fibreTerms indices axis v beta) (x+h) := by
  exact shift_terms_evaluate _ h x

theorem total_nonnegative (xs : List R) (h : ∀ x, x∈xs → 0≤x) : 0≤total xs := by
  induction xs with
  | nil => exact Std.le_refl 0
  | cons x xs ih =>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    rw [total]
    grind

theorem power_nonnegative (x : R) (hx:0≤x) (n : Nat) : 0≤x^n := by
  induction n with
  | zero => rw [Semiring.pow_zero]; grind
  | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih hx

theorem interval_mul (A B x y : R) (hA:0≤A) (hB:0≤B)
    (hx:-A≤x ∧ x≤A) (hy:-B≤y ∧ y≤B) : -A*B≤x*y ∧ x*y≤A*B := by
  by_cases h:0≤y
  · have h1:=OrderedRing.mul_le_mul_of_nonneg_right hx.1 h
    have h2:=OrderedRing.mul_le_mul_of_nonneg_right hx.2 h
    have h3:=OrderedRing.mul_le_mul_of_nonneg_left hy.2 hA
    constructor <;> grind
  · have hn:y≤0 := by grind
    have h1:=OrderedRing.mul_le_mul_of_nonpos_right hx.1 hn
    have h2:=OrderedRing.mul_le_mul_of_nonpos_right hx.2 hn
    have h3:=OrderedRing.mul_le_mul_of_nonneg_left (show -y≤B by grind) hA
    constructor <;> grind

theorem interval_power (D x : R) (hD:0≤D) (hx:-D≤x ∧ x≤D) (n : Nat) :
    -(D^n)≤x^n ∧ x^n≤D^n := by
  induction n with
  | zero => simp only [Semiring.pow_zero]; constructor <;> grind
  | succ n ih =>
    have hh:=interval_mul (D^n) D (x^n) x (power_nonnegative D hD n) hD ih hx
    rw [Semiring.pow_succ,Semiring.pow_succ]
    constructor <;> grind

theorem interval_total (terms : List (R × R))
    (h : ∀ t, t∈terms → 0≤t.1 ∧ -t.1≤t.2 ∧ t.2≤t.1) :
    -total (terms.map Prod.fst) ≤ total (terms.map Prod.snd) ∧
    total (terms.map Prod.snd) ≤ total (terms.map Prod.fst) := by
  induction terms with
  | nil => simp only [List.map_nil,total]; constructor <;> grind
  | cons t terms ih =>
    have hh:=h t (by simp)
    have ht:=ih (fun s hs=>h s (by simp [hs]))
    simp only [List.map_cons,total]
    constructor <;> grind

theorem interval_total_ofFn {J : Nat} (A x : Fin J → R)
    (h:∀ j, 0≤A j ∧ -A j≤x j ∧ x j≤A j) :
    -total (List.ofFn A)≤total (List.ofFn x) ∧ total (List.ofFn x)≤total (List.ofFn A) := by
  have hh:=interval_total (List.ofFn (fun j=>(A j,x j))) (by
    intro t ht
    rcases List.mem_ofFn.mp ht with ⟨j,hj⟩
    subst t
    exact h j)
  simpa only [List.map_ofFn,Function.comp_def] using hh

theorem total_scale (C : R) (xs : List R) : total (xs.map (fun x=>C*x))=C*total xs := by
  induction xs with
  | nil => simp [total,Semiring.mul_zero]
  | cons x xs ih => simp only [List.map_cons,total]; rw [ih]; grind

theorem total_ofFn_scale {J : Nat} (C : R) (f : Fin J → R) :
    total (List.ofFn (fun j=>C*f j))=C*total (List.ofFn f) := by
  have hh:=total_scale C (List.ofFn f)
  simpa only [List.map_ofFn,Function.comp_def] using hh

def entryBudget {d : Nat} (D : Nat) (axis : Fin d) (beta gamma : Fin d → Nat) : R :=
  (choose (gamma axis) (beta axis):R)*(D:R)^(gamma axis-beta axis)

def rowBudget {d J : Nat} (D : Nat) (indices : Fin J → Fin d → Nat)
    (axis : Fin d) (beta : Fin J) : R :=
  total (List.ofFn (fun gamma=>entryBudget D axis (indices beta) (indices gamma)))

theorem entry_budget_nonnegative {d : Nat} (D : Nat) (axis : Fin d) (beta gamma : Fin d → Nat) :
    0≤entryBudget (R := R) D axis beta gamma := by
  exact OrderedRing.mul_nonneg OrderedRing.natCast_nonneg
    (power_nonnegative (D:R) OrderedRing.natCast_nonneg _)

theorem entry_bound {d : Nat} (D : Nat) (axis : Fin d) (h : R)
    (hh:-(D:R)≤h ∧ h≤(D:R)) (beta gamma : Fin d → Nat) :
    -entryBudget D axis beta gamma ≤ entry axis h beta gamma ∧
    entry axis h beta gamma ≤ entryBudget D axis beta gamma := by
  have hc:0≤(choose (gamma axis) (beta axis):R) := OrderedRing.natCast_nonneg
  have hp:=interval_power (D:R) h OrderedRing.natCast_nonneg hh (gamma axis-beta axis)
  have hpow:=power_nonnegative (D:R) (R:=R) OrderedRing.natCast_nonneg (gamma axis-beta axis)
  have hm:=interval_mul (choose (gamma axis) (beta axis):R) ((D:R)^(gamma axis-beta axis))
    (choose (gamma axis) (beta axis):R) (h^(gamma axis-beta axis)) hc hpow (by constructor <;> grind) hp
  unfold entry
  split
  · unfold entryBudget; constructor <;> grind
  · have hb:=entry_budget_nonnegative (R:=R) D axis beta gamma
    constructor <;> grind

theorem row_budget_nonnegative {d J : Nat} (D : Nat) (indices : Fin J → Fin d → Nat)
    (axis : Fin d) (beta : Fin J) : 0≤rowBudget (R:=R) D indices axis beta := by
  apply total_nonnegative
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨gamma,hgamma⟩
  subst x
  exact entry_budget_nonnegative D axis _ _

/-- A concrete, finite row-sum budget bounds every transport candidate. -/
theorem transport_bound {d J : Nat} (D : Nat) (indices : Fin J → Fin d → Nat)
    (axis : Fin d) (h C : R) (hC:0≤C) (hh:-(D:R)≤h ∧ h≤(D:R))
    (v : Fin J → R) (hv:∀ gamma,-C≤v gamma ∧ v gamma≤C) (beta : Fin J) :
    -(C*rowBudget D indices axis beta)≤transport indices axis h v beta ∧
    transport indices axis h v beta≤C*rowBudget D indices axis beta := by
  have ht:=interval_total_ofFn
    (fun gamma=>C*entryBudget D axis (indices beta) (indices gamma))
    (fun gamma=>entry axis h (indices beta) (indices gamma)*v gamma) (by
      intro gamma
      have hA:=entry_budget_nonnegative (R:=R) D axis (indices beta) (indices gamma)
      have hm:=interval_mul (entryBudget D axis (indices beta) (indices gamma)) C
        (entry axis h (indices beta) (indices gamma)) (v gamma) hA hC
        (entry_bound D axis h hh _ _) (hv gamma)
      have hn:=OrderedRing.mul_nonneg hC hA
      refine ⟨hn,?_,?_⟩ <;> grind)
  rw [total_ofFn_scale] at ht
  exact ht

def signedStep (negative : Bool) (q : Nat) : R := if negative then -(q:R) else (q:R)

theorem signed_step_bound (negative : Bool) (q D : Nat) (hq:q≤D) :
    -(D:R)≤signedStep negative q ∧ signedStep negative q≤(D:R) := by
  have hq0:0≤(q:R) := OrderedRing.natCast_nonneg
  have hh:=OrderedRing.natCast_le_natCast_of_le (R:=R) q D hq
  cases negative <;> simp only [signedStep] <;> constructor <;> grind

end MathCan.TaylorTransport

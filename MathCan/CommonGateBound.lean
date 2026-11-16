import MathCan.ConcreteJetCapture

/-! Common axis-transport gate bounds. The layout is injective and every
coordinate degree is bounded; no assumption about a desired matrix norm is used.
The filtered fibre has at most one entry at each axis degree. -/
namespace MathCan.CommonGateBound
open Std Lean.Grind MathCan.SpatialScalar MathCan.TaylorPolynomial MathCan.TaylorTransport
variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R] [DecidableLT R]
attribute [local instance] Semiring.natCast Ring.intCast

theorem choose_le_power (n b : Nat) : choose n b≤2^n := by
  induction n generalizing b with
  | zero => cases b <;> simp [choose]
  | succ n ih =>
    cases b with
    | zero => rw [choose_zero]; have hp:0<2^(n+1) := Nat.pow_pos (by omega); omega
    | succ b =>
      rw [choose,Nat.pow_succ]
      have h1:=ih b
      have h2:=ih (b+1)
      omega

def choosePrefix : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,b => choosePrefix n b+choose n b

theorem choose_prefix_eq (n b : Nat) : choosePrefix n b=choose n (b+1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choosePrefix,ih,choose]; omega

theorem choose_prefix_bound (n b : Nat) : choosePrefix n b≤2^n := by
  rw [choose_prefix_eq]
  exact choose_le_power n (b+1)

theorem sum_choose_cast (n b : Nat) :
    sum n (fun j=>(choose j b:R))=(choosePrefix n b:R) := by
  induction n with
  | zero => simp [sum,choosePrefix,Semiring.natCast_zero]
  | succ n ih => rw [sum,ih,choosePrefix,Semiring.natCast_add]

theorem sum_le (n : Nat) (f g : Nat → R) (h:∀ j,j<n → f j≤g j) : sum n f≤sum n g := by
  induction n with
  | zero => exact Std.le_refl 0
  | succ n ih =>
    have ht:=ih (fun j hj=>h j (by omega))
    have hh:=h n (by omega)
    simp only [sum]
    grind

theorem sum_scale (n : Nat) (C : R) (f : Nat → R) :
    sum n (fun j=>C*f j)=C*sum n f := by
  induction n with
  | zero => simp [sum,Semiring.mul_zero]
  | succ n ih => rw [sum,sum,ih]; grind

theorem totalFn_zero (J : Nat) : total (List.ofFn (fun _ : Fin J=>(0:R)))=0 := by
  induction J with
  | zero => rfl
  | succ J ih => simp only [List.ofFn_succ,total,ih,AddCommMonoid.zero_add]

theorem totalFn_add {J : Nat} (f g : Fin J → R) :
    total (List.ofFn (fun j=>f j+g j))=total (List.ofFn f)+total (List.ofFn g) := by
  induction J with
  | zero => simp only [List.ofFn_zero,total]; grind
  | succ J ih => simp only [List.ofFn_succ,total]; rw [ih]; grind

theorem totalFn_sum {J : Nat} (n : Nat) (f : Fin J → Nat → R) :
    total (List.ofFn (fun j=>sum n (f j)))=sum n (fun q=>total (List.ofFn (fun j=>f j q))) := by
  induction n with
  | zero => simp only [sum,totalFn_zero]
  | succ n ih => simp only [sum]; rw [totalFn_add,ih]

theorem totalFn_le {J : Nat} (f g : Fin J → R) (h:∀ j,f j≤g j) :
    total (List.ofFn f)≤total (List.ofFn g) := by
  induction J with
  | zero => exact Std.le_refl 0
  | succ J ih =>
    have ht:=ih (fun j=>f j.succ) (fun j=>g j.succ) (fun j=>h j.succ)
    have hh:=h 0
    simp only [List.ofFn_succ,total]
    grind

theorem singleton_total_le {J : Nat} (P : Fin J → Prop) [DecidablePred P]
    (unique:∀ j l,P j → P l → j=l) (w : R) (hw:0≤w) :
    total (List.ofFn (fun j=>if P j then w else 0))≤w := by
  induction J with
  | zero => exact hw
  | succ J ih =>
    by_cases h0:P 0
    · have hz:∀ j:Fin J,¬P j.succ := by
        intro j hj
        have he:=congrArg Fin.val (unique 0 j.succ h0 hj)
        simp only [Fin.val_zero,Fin.val_succ] at he
        omega
      have heq:(fun j:Fin J=>if P j.succ then w else 0)=(fun _=>0) := by
        funext j
        exact if_neg (hz j)
      rw [List.ofFn_succ,total,if_pos h0,heq,totalFn_zero]
      grind
    · rw [List.ofFn_succ,total,if_neg h0,AddCommMonoid.zero_add]
      apply ih (fun j=>P j.succ)
      intro j l hj hl
      exact Fin.ext (Nat.succ.inj (congrArg Fin.val (unique j.succ l.succ hj hl)))

theorem tagged_sum_le {J : Nat} (bound : Nat) (P : Fin J → Prop) [DecidablePred P]
    (tag : Fin J → Nat) (inrange:∀ j,P j → tag j<bound)
    (unique:∀ j l,P j → P l → tag j=tag l → j=l)
    (w : Nat → R) (hw:∀ q,q<bound → 0≤w q) :
    total (List.ofFn (fun j=>if P j then w (tag j) else 0))≤sum bound w := by
  have heq:∀ j,(if P j then w (tag j) else 0)=
      sum bound (fun q=>if P j ∧ tag j=q then w q else 0) := by
    intro j
    by_cases hj:P j
    · rw [if_pos hj]
      symm
      calc
        _ = sum bound (fun q=>if q=tag j then w (tag j) else 0) := by
          apply sum_congr
          intro q hq
          by_cases he:q=tag j
          · subst q; simp [hj]
          · simp [hj,he,Ne.symm he]
        _ = w (tag j) := sum_single bound (tag j) (inrange j hj) _
    · rw [if_neg hj]
      have hz:(fun q=>if P j ∧ tag j=q then w q else 0)=(fun _=>0) := by funext q; simp [hj]
      rw [hz,sum_zero]
  calc
    _ = total (List.ofFn (fun j=>sum bound (fun q=>if P j ∧ tag j=q then w q else 0))) :=
      congrArg (fun f=>total (List.ofFn f)) (funext heq)
    _ = sum bound (fun q=>total (List.ofFn (fun j=>if P j ∧ tag j=q then w q else 0))) := totalFn_sum _ _
    _ ≤ sum bound w := by
      apply sum_le
      intro q hq
      apply singleton_total_le (fun j=>P j ∧ tag j=q)
      · intro j l hj hl
        exact unique j l hj.1 hl.1 (hj.2.trans hl.2.symm)
      · exact hw q hq

theorem power_mono_exponent (D : R) (hD:1≤D) (n k : Nat) (hn:n≤k) : D^n≤D^k := by
  induction k generalizing n with
  | zero =>
    have he:n=0 := by omega
    subst n
    exact Std.le_refl _
  | succ k ih =>
    by_cases h:n=k+1
    · subst n; exact Std.le_refl _
    · have ht:=ih n (by omega)
      have h0:0≤D := by grind
      have hp:=power_nonnegative D h0 k
      have hm:=OrderedRing.mul_le_mul_of_nonneg_left hD hp
      rw [Semiring.mul_one] at hm
      rw [Semiring.pow_succ]
      grind

def commonBudget (k D : Nat) : R := ((2^(k+1)*D^k:Nat):R)

def fibreBudget {d J : Nat} (D : Nat) (indices : Fin J → Fin d → Nat)
    (axis : Fin d) (beta : Fin J) : R := total (List.ofFn (fun gamma=>
  if compatible axis (indices beta) (indices gamma) ∧ indices beta axis≤indices gamma axis
  then entryBudget D axis (indices beta) (indices gamma) else 0))

theorem fibre_unique {d J : Nat} (indices : Fin J → Fin d → Nat)
    (injective:∀ j l,indices j=indices l → j=l) (axis : Fin d) (beta j l : Fin J)
    (hj:compatible axis (indices beta) (indices j)) (hl:compatible axis (indices beta) (indices l))
    (he:indices j axis=indices l axis) : j=l := by
  apply injective
  funext q
  by_cases hq:q=axis
  · subst q; exact he
  · exact (hj q hq).trans (hl q hq).symm

/-- The filtered row budget satisfies the common 2^(k+1)*D^k bound. -/
theorem fibre_budget_common {d J : Nat} (k D : Nat) (hD:1≤D)
    (indices : Fin J → Fin d → Nat) (injective:∀ j l,indices j=indices l → j=l)
    (axis : Fin d) (degree:∀ gamma,indices gamma axis≤k) (beta : Fin J) :
    fibreBudget (R:=R) D indices axis beta≤commonBudget k D := by
  let P:=fun gamma=>compatible axis (indices beta) (indices gamma) ∧ indices beta axis≤indices gamma axis
  let w:=fun n=>(D:R)^k*(choose n (indices beta axis):R)
  have hD1:(1:R)≤(D:R) := by
    have hh:=OrderedRing.natCast_le_natCast_of_le (R:=R) 1 D hD
    simpa only [Semiring.natCast_one] using hh
  have hD0:0≤(D:R) := by grind
  have hp:=power_nonnegative (D:R) hD0 k
  have hmajor:fibreBudget (R:=R) D indices axis beta≤
      total (List.ofFn (fun gamma=>if P gamma then w (indices gamma axis) else 0)) := by
    apply totalFn_le
    intro gamma
    by_cases hg:P gamma
    · simp only [P,if_pos hg]
      have hm:=power_mono_exponent (D:R) hD1 (indices gamma axis-indices beta axis) k (by have:=degree gamma; omega)
      have hc:0≤(choose (indices gamma axis) (indices beta axis):R) := OrderedRing.natCast_nonneg
      have hh:=OrderedRing.mul_le_mul_of_nonneg_left hm hc
      unfold entryBudget w
      grind
    · simp only [P,if_neg hg]
      exact Std.le_refl 0
  have hs:=tagged_sum_le (k+1) P (fun gamma=>indices gamma axis)
    (fun gamma _=>by have:=degree gamma; omega)
    (fun j l hj hl he=>fibre_unique indices injective axis beta j l hj.1 hl.1 he)
    w (fun n _=>OrderedRing.mul_nonneg hp OrderedRing.natCast_nonneg)
  have hprefix:=OrderedRing.natCast_le_natCast_of_le (R:=R) (choosePrefix (k+1) (indices beta axis))
    (2^(k+1)) (choose_prefix_bound (k+1) (indices beta axis))
  have hm:=OrderedRing.mul_le_mul_of_nonneg_left hprefix hp
  have heq:sum (k+1) w=(D:R)^k*(choosePrefix (k+1) (indices beta axis):R) := by
    rw [sum_scale,sum_choose_cast]
  rw [heq] at hs
  unfold commonBudget
  rw [Semiring.natCast_mul,Semiring.natCast_pow D k]
  grind

theorem common_budget_nonnegative (k D : Nat) : 0≤commonBudget (R:=R) k D := by
  exact OrderedRing.natCast_nonneg

/-- Every Taylor candidate is bounded by the same constant, independently of
the jet coordinate and number of streamed spatial sites. -/
theorem transport_common_bound {d J : Nat} (k D : Nat) (hD:1≤D)
    (indices : Fin J → Fin d → Nat) (injective:∀ j l,indices j=indices l → j=l)
    (axis : Fin d) (degree:∀ gamma,indices gamma axis≤k) (h C : R) (hC:0≤C)
    (hh:-(D:R)≤h ∧ h≤(D:R)) (v : Fin J → R)
    (hv:∀ gamma,-C≤v gamma ∧ v gamma≤C) (beta : Fin J) :
    -(C*commonBudget k D)≤transport indices axis h v beta ∧
    transport indices axis h v beta≤C*commonBudget k D := by
  let A:=fun gamma=>if compatible axis (indices beta) (indices gamma) ∧ indices beta axis≤indices gamma axis
    then entryBudget (R:=R) D axis (indices beta) (indices gamma) else 0
  have ht:=interval_total_ofFn (fun gamma=>C*A gamma)
    (fun gamma=>entry axis h (indices beta) (indices gamma)*v gamma) (by
      intro gamma
      by_cases ha:compatible axis (indices beta) (indices gamma) ∧ indices beta axis≤indices gamma axis
      · have hA:=entry_budget_nonnegative (R:=R) D axis (indices beta) (indices gamma)
        have hm:=interval_mul (entryBudget D axis (indices beta) (indices gamma)) C
          (entry axis h (indices beta) (indices gamma)) (v gamma) hA hC
          (entry_bound D axis h hh _ _) (hv gamma)
        have hn:=OrderedRing.mul_nonneg hC hA
        simp only [A,if_pos ha]
        refine ⟨hn,?_,?_⟩ <;> grind
      · simp only [A,if_neg ha,entry,Semiring.mul_zero,Semiring.zero_mul]
        simp [ha] <;> grind)
  rw [total_ofFn_scale] at ht
  have hb:=fibre_budget_common (R:=R) k D hD indices injective axis degree beta
  have hm:=OrderedRing.mul_le_mul_of_nonneg_left hb hC
  change C*total (List.ofFn A)≤C*commonBudget k D at hm
  change -(C*total (List.ofFn A))≤transport indices axis h v beta ∧
    transport indices axis h v beta≤C*total (List.ofFn A) at ht
  constructor <;> grind

end MathCan.CommonGateBound

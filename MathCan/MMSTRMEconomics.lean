/-!
# SCCG-10 / MMS-TRM: refresh value, chronological transport, reinvestment

Finite exact companions to BPD `sccg10_native_mms/MATH_REVIEW.md`.
Integers stand in for exactly scaled rationals. Nothing here is a statement
about a trained model; each theorem is the arithmetic core of a proposition
whose hypotheses must be established separately for a real run.

* `voi_refresh_le` (Prop. 9): picking by stale scores loses at most
  `2δ + 2ε` against picking by fresh scores, when stale and fresh scores
  differ by at most `δ` and fresh scores are within `ε` of realized gains.
* `voi_refresh_sharp`: equality is attained.
* `chrono_prod_bound` (Prop. 3, scalar case): for scalar per-step factors,
  `|∏ a'_t - ∏ a_t| ≤ ∏ (|a_t| + |a'_t - a_t|) - ∏ |a_t|`.
* `chrono_prod_sharp`: aligned nonnegative perturbations attain it.
* `ratio_rule` (Prop. 14): with additive stationary values, no split of a
  budget beats spending it all on the action with the larger value/cost.
* `near_null_persistence` (Prop. 4a): `|C'u| ≤ |Cu| + |(C'-C)u|` per row.
* `myopic_not_two_step` (Prop. 10c): the one-step greedy choice can lose
  over two windows.
-/

namespace MathCan.MMSTRMEconomics

/-- Prop. 9: value of refreshing stale candidate scores. `bs` maximizes the
    stale score, `bf` maximizes the fresh score. -/
theorem voi_refresh_le {K : Type} (s sf r : K → Int) (δ ε : Int) (bs bf : K)
    (hs : ∀ b, s b ≤ s bs) (hf : ∀ b, sf b ≤ sf bf)
    (hd : ∀ b, -δ ≤ s b - sf b ∧ s b - sf b ≤ δ)
    (he : ∀ b, -ε ≤ sf b - r b ∧ sf b - r b ≤ ε) :
    r bf - r bs ≤ 2 * δ + 2 * ε := by
  have h1 := hs bf
  have h2 := hd bs
  have h3 := hd bf
  have h4 := he bs
  have h5 := he bf
  have _ := hf bs
  omega

/-- The bound in `voi_refresh_le` is attained (two candidates). -/
theorem voi_refresh_sharp :
    ∃ (s sf r : Bool → Int) (δ ε : Int),
      (∀ b, s b ≤ s false) ∧ (∀ b, sf b ≤ sf true) ∧
      (∀ b, -δ ≤ s b - sf b ∧ s b - sf b ≤ δ) ∧
      (∀ b, -ε ≤ sf b - r b ∧ sf b - r b ≤ ε) ∧
      r true - r false = 2 * δ + 2 * ε := by
  refine ⟨fun b => if b then 0 else 0, fun b => if b then 1 else -1,
          fun b => if b then 2 else -2, 1, 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro b; cases b <;> decide
  · intro b; cases b <;> decide
  · intro b; cases b <;> decide
  · intro b; cases b <;> decide
  · decide

/-- Product of a list of integers. -/
def prod : List Int → Int
  | [] => 1
  | a :: t => a * prod t

/-- Product of absolute values. -/
def absProd : List Int → Int
  | [] => 1
  | a :: t => (a.natAbs : Int) * absProd t

/-- Product of `|a| + |a' - a|` over paired lists. -/
def envProd : List (Int × Int) → Int
  | [] => 1
  | (a, a') :: t => ((a.natAbs : Int) + ((a' - a).natAbs : Int)) * envProd t

theorem absProd_nonneg : ∀ l : List Int, 0 ≤ absProd l
  | [] => by simp [absProd]
  | a :: t => by
      simp only [absProd]
      exact Int.mul_nonneg (Int.natCast_nonneg _) (absProd_nonneg t)

theorem natAbs_prod : ∀ l : List Int, ((prod l).natAbs : Int) = absProd l
  | [] => by simp [prod, absProd]
  | a :: t => by
      simp only [prod, absProd, Int.natAbs_mul, Int.natCast_mul]
      rw [natAbs_prod t]

/-- Prop. 3, scalar chronological transport: the end-to-end perturbation of
    a product of per-step factors is bounded by the envelope product minus
    the clean absolute product. -/
theorem chrono_prod_bound : ∀ l : List (Int × Int),
    ((prod (l.map Prod.snd) - prod (l.map Prod.fst)).natAbs : Int)
      ≤ envProd l - absProd (l.map Prod.fst)
  | [] => by simp [prod, envProd, absProd]
  | (a, a') :: t => by
      have ih := chrono_prod_bound t
      simp only [List.map_cons, prod, envProd, absProd]
      generalize hQ' : prod (t.map Prod.snd) = Q' at *
      generalize hQ : prod (t.map Prod.fst) = Q at *
      generalize hE : envProd t = E at *
      have hA : ((Q.natAbs : Int)) = absProd (t.map Prod.fst) := by
        rw [← hQ]; exact natAbs_prod _
      generalize hP : absProd (t.map Prod.fst) = P at *
      -- a'Q' - aQ = a'(Q' - Q) + (a' - a) Q
      have split : a' * Q' - a * Q = a' * (Q' - Q) + (a' - a) * Q := by
        rw [Int.mul_sub, Int.sub_mul]; omega
      have t1 : ((a' * (Q' - Q)).natAbs : Int) ≤ ((a'.natAbs : Int)) * (E - P) := by
        rw [Int.natAbs_mul, Int.natCast_mul]
        exact Int.mul_le_mul_of_nonneg_left ih (Int.natCast_nonneg _)
      have t2 : (((a' - a) * Q).natAbs : Int) = ((a' - a).natAbs : Int) * P := by
        rw [Int.natAbs_mul, Int.natCast_mul, hA]
      have tri : ((a' * Q' - a * Q).natAbs : Int)
          ≤ ((a' * (Q' - Q)).natAbs : Int) + (((a' - a) * Q).natAbs : Int) := by
        rw [split]
        have := Int.natAbs_add_le (a' * (Q' - Q)) ((a' - a) * Q)
        omega
      have ha' : (a'.natAbs : Int) ≤ (a.natAbs : Int) + ((a' - a).natAbs : Int) := by
        have := Int.natAbs_add_le a (a' - a)
        have e : a + (a' - a) = a' := by omega
        rw [e] at this
        omega
      have hEP : 0 ≤ E - P := by
        have := Int.natCast_nonneg (Q' - Q).natAbs
        omega
      have t3 : ((a'.natAbs : Int)) * (E - P)
          ≤ ((a.natAbs : Int) + ((a' - a).natAbs : Int)) * (E - P) :=
        Int.mul_le_mul_of_nonneg_right ha' hEP
      have expand : ((a.natAbs : Int) + ((a' - a).natAbs : Int)) * (E - P)
            + ((a' - a).natAbs : Int) * P
          = ((a.natAbs : Int) + ((a' - a).natAbs : Int)) * E - (a.natAbs : Int) * P := by
        rw [Int.mul_sub, Int.add_mul, Int.add_mul]; omega
      omega

/-- Aligned nonnegative perturbations attain the chronological bound. -/
theorem chrono_prod_sharp :
    ((prod [3, 3] - prod [2, 2]).natAbs : Int) = envProd [(2, 3), (2, 3)] - absProd [2, 2] := by
  decide

/-- Prop. 14, ratio rule: with values `v1, v2`, costs `c1, c2` and
    `v1/c1 >= v2/c2` (stated as `v2 c1 <= v1 c2`), any split with `n2 >= 0`
    within budget `B` has value at most `B * v1 / c1` (stated without
    division; positivity of `c1` and `n1` is not needed for this direction). -/
theorem ratio_rule (v1 v2 c1 c2 n1 n2 B : Int)
    (hv1 : 0 ≤ v1) (hn2 : 0 ≤ n2)
    (hratio : v2 * c1 ≤ v1 * c2) (hB : n1 * c1 + n2 * c2 ≤ B) :
    (n1 * v1 + n2 * v2) * c1 ≤ B * v1 := by
  have e1 : (n1 * v1 + n2 * v2) * c1 = n1 * c1 * v1 + n2 * (v2 * c1) := by
    rw [Int.add_mul, Int.mul_assoc, Int.mul_comm v1 c1, ← Int.mul_assoc, Int.mul_assoc n2]
  have e2 : n2 * (v2 * c1) ≤ n2 * (v1 * c2) := Int.mul_le_mul_of_nonneg_left hratio hn2
  have e3 : (n1 * c1 + n2 * c2) * v1 ≤ B * v1 := Int.mul_le_mul_of_nonneg_right hB hv1
  have e4 : (n1 * c1 + n2 * c2) * v1 = n1 * c1 * v1 + n2 * (v1 * c2) := by
    rw [Int.add_mul, Int.mul_assoc n2, Int.mul_comm c2 v1]
  omega

/-- Prop. 4a, per protected row: a stored near-null direction stays within
    the drift of the row. No spectral gap is needed. -/
theorem near_null_persistence (cu cu' : Int) :
    (cu'.natAbs : Int) ≤ (cu.natAbs : Int) + ((cu' - cu).natAbs : Int) := by
  have := Int.natAbs_add_le cu (cu' - cu)
  have e : cu + (cu' - cu) = cu' := by omega
  rw [e] at this
  omega

/-- Prop. 10c: greedy one-step choice (`A`, gain 2 then 0) loses to `B`
    (gain 1 then 3) over two windows. -/
theorem myopic_not_two_step :
    ∃ (now next : Bool → Int),
      now true > now false ∧ now true + next true < now false + next false :=
  ⟨fun b => if b then 2 else 1, fun b => if b then 0 else 3, by decide, by decide⟩

/-- Refusing an audit: if the refresh-value bound is at most what the same
    CPU earns by ordinary reinvestment, refreshing cannot beat reinvesting. -/
theorem refuse_audit (voi cost rate gain : Int)
    (hvoi : gain ≤ voi) (hcheap : voi ≤ cost * rate) :
    gain - cost * rate ≤ 0 := by
  omega

#print axioms voi_refresh_le
#print axioms voi_refresh_sharp
#print axioms chrono_prod_bound
#print axioms chrono_prod_sharp
#print axioms ratio_rule
#print axioms near_null_persistence
#print axioms myopic_not_two_step
#print axioms refuse_audit

end MathCan.MMSTRMEconomics

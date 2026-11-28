import Init

/-!
# MathCan: decision-directed compactification (DCF-13 / DCF-13D)

Kernel-checked integer forms of the facts the DCF-13 experiments rely on
(Compactification-Theory, `research/dcf13_decision_compactification`).

* `signedMass_product`: the parity-signed mass of a product of two independent
  components is the product of their signed masses. With total masses this gives
  `P(parity = 1) = (1 - s_A s_B) / 2`, the formula used by query-directed
  component inference, so disconnected evidence can be ignored exactly.
* `act_optimal`: with answer masses `n0, n1` (only `n1 ≥ 0` is needed) and reward +1 / -4 / 0, the
  threshold policy (act on 1 iff `n1 ≥ 4 n0`, on 0 iff `n0 ≥ 4 n1`) is optimal
  among the three actions and never has negative expected utility.
* `interval_certificate_sound`: lower/upper mass bounds with `4 U0 ≤ L1`
  certify `4 N0 ≤ N1` for every model inside the bounds (DCF-13B pointwise
  bounds and DCF-13D credal decisions both reduce to this step).
* `bern_nonneg`: a polynomial with nonnegative Bernstein-form coefficients is
  nonnegative at every rational point `a / d ∈ [0, 1]` (scaled by `d^m`). This is
  the soundness step of the DCF-13D shared-weight credal certificate.

Masses are integers here (any finite-precision rational instance scales to
this); the real-valued extension of `bern_nonneg` follows by density and
continuity and is not formalized.
-/
namespace MathCan.DCF

/-- Sum of a list of integers. -/
def lsum : List Int → Int
  | [] => 0
  | x :: xs => x + lsum xs

theorem lsum_append (xs ys : List Int) : lsum (xs ++ ys) = lsum xs + lsum ys := by
  induction xs with
  | nil => simp [lsum]
  | cons x xs ih => simp [lsum, ih, Int.add_assoc]

theorem lsum_map_mul_left {α : Type} (c : Int) (f : α → Int) (bs : List α) :
    lsum (bs.map fun b => c * f b) = c * lsum (bs.map f) := by
  induction bs with
  | nil => simp [lsum]
  | cons b bs ih => simp [lsum, ih, Int.mul_add]

/-- Sum over a product of two finite lists factorises. -/
theorem lsum_product {α β : Type} (f : α → Int) (g : β → Int) (as : List α) (bs : List β) :
    lsum (as.flatMap fun a => bs.map fun b => f a * g b) = lsum (as.map f) * lsum (bs.map g) := by
  induction as with
  | nil => simp [lsum]
  | cons a as ih =>
    simp only [List.flatMap_cons, lsum_append, lsum_map_mul_left, ih, List.map_cons, lsum, Int.add_mul]

/-- `(-1)^parity`. -/
def sgn : Bool → Int
  | false => 1
  | true => -1

theorem sgn_xor (p q : Bool) : sgn (xor p q) = sgn p * sgn q := by
  cases p <;> cases q <;> decide

/-- Parity-signed mass of a component: the sum of `w x * (-1)^(parity x)`. -/
def signedMass {α : Type} (w : α → Int) (par : α → Bool) (xs : List α) : Int :=
  lsum (xs.map fun x => w x * sgn (par x))

/-- Independent components: weights multiply and parities add mod 2, so signed
masses multiply. -/
theorem signedMass_product {α β : Type} (wa : α → Int) (pa : α → Bool) (wb : β → Int) (pb : β → Bool)
    (as : List α) (bs : List β) :
    lsum (as.flatMap fun a => bs.map fun b => (wa a * wb b) * sgn (xor (pa a) (pb b)))
      = signedMass wa pa as * signedMass wb pb bs := by
  have h : ∀ a b, (wa a * wb b) * sgn (xor (pa a) (pb b))
      = (wa a * sgn (pa a)) * (wb b * sgn (pb b)) := by
    intro a b
    rw [sgn_xor, Int.mul_assoc, Int.mul_assoc, Int.mul_left_comm (wb b)]
  simp only [h]
  exact lsum_product (fun a => wa a * sgn (pa a)) (fun b => wb b * sgn (pb b)) as bs

/-- Total mass is the signed mass with every parity even. -/
theorem mass_product {α β : Type} (wa : α → Int) (wb : β → Int) (as : List α) (bs : List β) :
    lsum (as.flatMap fun a => bs.map fun b => wa a * wb b) = lsum (as.map wa) * lsum (bs.map wb) :=
  lsum_product wa wb as bs

/-! ## Decisions with reward +1 / -4 / 0 -/

/-- Expected utility of answering 1, scaled by the total mass. -/
def eu1 (n0 n1 : Int) : Int := n1 - 4 * n0
/-- Expected utility of answering 0, scaled by the total mass. -/
def eu0 (n0 n1 : Int) : Int := n0 - 4 * n1

/-- Threshold policy: 1 if `p ≥ 4/5`, 0 if `p ≤ 1/5`, otherwise abstain (-1). -/
def act (n0 n1 : Int) : Int := if 4 * n0 ≤ n1 then 1 else if 4 * n1 ≤ n0 then 0 else -1

/-- Scaled expected utility of an action code. -/
def value (n0 n1 a : Int) : Int := if a = 1 then eu1 n0 n1 else if a = 0 then eu0 n0 n1 else 0

theorem act_optimal (n0 n1 : Int) (h1 : 0 ≤ n1) :
    eu1 n0 n1 ≤ value n0 n1 (act n0 n1) ∧ eu0 n0 n1 ≤ value n0 n1 (act n0 n1) ∧
      0 ≤ value n0 n1 (act n0 n1) := by
  unfold value act eu1 eu0
  by_cases ha : 4 * n0 ≤ n1 <;> by_cases hb : 4 * n1 ≤ n0 <;> simp [ha, hb] <;> omega

/-- Interval certificates: if every admissible model's masses satisfy `L1 ≤ N1` and
`N0 ≤ U0`, then `4 U0 ≤ L1` forces the answer 1 to be acceptable for that model. -/
theorem interval_certificate_sound (L1 N1 N0 U0 : Int) (hl : L1 ≤ N1) (hu : N0 ≤ U0)
    (h : 4 * U0 ≤ L1) : 4 * N0 ≤ N1 := by
  omega

theorem certified_action_nonnegative (L1 N1 N0 U0 : Int) (hl : L1 ≤ N1) (hu : N0 ≤ U0)
    (h : 4 * U0 ≤ L1) : 0 ≤ eu1 N0 N1 := by
  unfold eu1
  omega

/-! ## Bernstein-form certificates -/

/-- Natural-number powers of an integer. -/
def ipow (x : Int) : Nat → Int
  | 0 => 1
  | k + 1 => x * ipow x k

theorem ipow_nonneg (x : Int) (hx : 0 ≤ x) : ∀ k, 0 ≤ ipow x k
  | 0 => by simp [ipow]
  | k + 1 => Int.mul_nonneg hx (ipow_nonneg x hx k)

/-- `Σ_i c_i a^i b^(m-i)` over the coefficient list starting at index `i`; with
`b = d - a` this is `d^m` times the Bernstein-form polynomial at `w = a / d`. -/
def bern (a b : Int) (m : Nat) : Nat → List Int → Int
  | _, [] => 0
  | i, c :: cs => c * ipow a i * ipow b (m - i) + bern a b m (i + 1) cs

theorem bern_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : Nat) :
    ∀ (i : Nat) (cs : List Int), (∀ c, c ∈ cs → 0 ≤ c) → 0 ≤ bern a b m i cs
  | _, [], _ => by simp [bern]
  | i, c :: cs, h => by
    unfold bern
    exact Int.add_nonneg
      (Int.mul_nonneg (Int.mul_nonneg (h c (by simp)) (ipow_nonneg a ha i)) (ipow_nonneg b hb (m - i)))
      (bern_nonneg a b ha hb m (i + 1) cs (fun x hx => h x (by simp [hx])))

/-- Certificate soundness on the rational grid: nonnegative Bernstein coefficients give a
nonnegative value at every `w = a / d` with `0 ≤ a ≤ d`. -/
theorem bernstein_certificate_sound (cs : List Int) (a d : Int) (m : Nat)
    (ha : 0 ≤ a) (had : a ≤ d) (hc : ∀ c, c ∈ cs → 0 ≤ c) : 0 ≤ bern a (d - a) m 0 cs :=
  bern_nonneg a (d - a) ha (by omega) m 0 cs hc

end MathCan.DCF

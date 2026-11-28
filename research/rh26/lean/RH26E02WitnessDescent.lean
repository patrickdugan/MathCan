import Mathlib

/-!
# RH-26E-02: witness-certified scalar transport and rank descent

Independent field-algebra toy, inspired by the pinned alpha/beta cancellation
arguments recorded in RH26B06_RANK_STEP_PROOFS.md. No upstream automorphic
definitions are imported. Nonzero analytic factors and certified witness
relations remain explicit hypotheses.
-/

namespace RH26E02

variable {K : Type*} [Field K]

/-- The beta split-component identity determines the normalized transport. -/
theorem beta_normalized_from_component (d l c c₁ w : K)
    (hwc : c * w ≠ 0)
    (hstep : (d * l) * (c * w) = c₁ * w) :
    c₁ = d * c * l := by
  have hw : w ≠ 0 := by
    intro hz
    apply hwc
    simp [hz]
  exact mul_right_cancel₀ hw (calc
    c₁ * w = (d * l) * (c * w) := hstep.symm
    _ = (d * c * l) * w := by ring)

/-- The additional nonzero arithmetic factor yields the beta inverse witness. -/
theorem beta_inverse_from_component (d l c c₁ w : K)
    (hd : d ≠ 0) (hwc : c * w ≠ 0)
    (hstep : (d * l) * (c * w) = c₁ * w) :
    ∃ u : K, u * d = 1 ∧ c * l = u * c₁ := by
  have hn := beta_normalized_from_component d l c c₁ w hwc hstep
  refine ⟨d⁻¹, inv_mul_cancel₀ hd, ?_⟩
  calc
    c * l = (d⁻¹ * d) * (c * l) := by rw [inv_mul_cancel₀ hd, one_mul]
    _ = d⁻¹ * (d * c * l) := by ring
    _ = d⁻¹ * c₁ := congrArg (fun x : K => d⁻¹ * x) hn.symm

theorem beta_l_nonzero (d l c c₁ w : K)
    (hwc : c * w ≠ 0) (hsmall : c₁ ≠ 0)
    (hstep : (d * l) * (c * w) = c₁ * w) :
    l ≠ 0 := by
  intro hz
  apply hsmall
  rw [beta_normalized_from_component d l c c₁ w hwc hstep, hz, mul_zero]

/-- The alpha branch cancels its nonzero evaluation directly. -/
theorem alpha_from_component (d l c c₁ w : K)
    (hw : w ≠ 0)
    (hstep : c * w = (d * l * c₁) * w) :
    c = d * l * c₁ :=
  mul_right_cancel₀ hw hstep

theorem alpha_l_nonzero (d l c c₁ w : K)
    (hw : w ≠ 0) (hlarge : c ≠ 0)
    (hstep : c * w = (d * l * c₁) * w) :
    l ≠ 0 := by
  intro hz
  apply hlarge
  rw [alpha_from_component d l c c₁ w hw hstep, hz, mul_zero, zero_mul]

theorem scalar_unique (c c₁ w : K) (hw : w ≠ 0)
    (heq : c * w = c₁ * w) : c = c₁ :=
  mul_right_cancel₀ hw heq

inductive Direction where
  | alpha
  | beta
  deriving DecidableEq

/-- Larger-rank scalar c and smaller-rank scalar c₁ have distinct orientations. -/
def Transport (dir : Direction) (d l c c₁ : K) : Prop :=
  match dir with
  | .alpha => c = d * l * c₁
  | .beta => c₁ = d * c * l

/-- The local witness gate, before component cancellation. -/
def WitnessStep (dir : Direction) (d l c c₁ w : K) : Prop :=
  match dir with
  | .alpha => w ≠ 0 ∧ c * w = (d * l * c₁) * w
  | .beta => d ≠ 0 ∧ c * w ≠ 0 ∧ (d * l) * (c * w) = c₁ * w

theorem witness_to_transport (dir : Direction) (d l c c₁ w : K)
    (h : WitnessStep dir d l c c₁ w) :
    Transport dir d l c c₁ := by
  cases dir with
  | alpha =>
    rcases h with ⟨hw, he⟩
    exact alpha_from_component d l c c₁ w hw he
  | beta =>
    rcases h with ⟨_, hwc, he⟩
    exact beta_normalized_from_component d l c c₁ w hwc he

/-- A normalized edge transports nonvanishing from smaller to larger rank. -/
theorem edge_nonzero (dir : Direction) (d l c c₁ : K)
    (hd : d ≠ 0) (hl : l ≠ 0) (hsmall : c₁ ≠ 0)
    (h : Transport dir d l c c₁) : c ≠ 0 := by
  cases dir with
  | alpha =>
    change c = d * l * c₁ at h
    rw [h]
    exact mul_ne_zero (mul_ne_zero hd hl) hsmall
  | beta =>
    change c₁ = d * c * l at h
    intro hz
    apply hsmall
    rw [h, hz, mul_zero, zero_mul]

/-- Bounded induction implements well-founded descent on an arbitrary rank. -/
theorem rank_descent_nonzero {S : Type*} (μ : S → ℕ) (c : S → K)
    (hbase : ∀ x, μ x = 0 → c x ≠ 0)
    (hstep : ∀ x, μ x ≠ 0 →
      ∃ (y : S) (dir : Direction) (d l : K),
        μ y < μ x ∧ d ≠ 0 ∧ l ≠ 0 ∧ Transport dir d l (c x) (c y)) :
    ∀ x, c x ≠ 0 := by
  have bounded : ∀ n : ℕ, ∀ x : S, μ x ≤ n → c x ≠ 0 := by
    intro n
    induction n with
    | zero =>
      intro x hx
      exact hbase x (by omega)
    | succ n ih =>
      intro x hx
      by_cases hz : μ x = 0
      · exact hbase x hz
      · obtain ⟨y, dir, d, l, hlt, hd, hl, ht⟩ := hstep x hz
        have hy : μ y ≤ n := by omega
        exact edge_nonzero dir d l (c x) (c y) hd hl (ih y hy) ht
  intro x
  exact bounded (μ x) x le_rfl

/-- The witness-level version composes the cancellation and descent gates. -/
theorem witness_rank_descent_nonzero {S : Type*} (μ : S → ℕ) (c : S → K)
    (hbase : ∀ x, μ x = 0 → c x ≠ 0)
    (hstep : ∀ x, μ x ≠ 0 →
      ∃ (y : S) (dir : Direction) (d l w : K),
        μ y < μ x ∧ d ≠ 0 ∧ l ≠ 0 ∧ WitnessStep dir d l (c x) (c y) w) :
    ∀ x, c x ≠ 0 := by
  apply rank_descent_nonzero μ c hbase
  intro x hx
  obtain ⟨y, dir, d, l, w, hr, hd, hl, hw⟩ := hstep x hx
  exact ⟨y, dir, d, l, hr, hd, hl, witness_to_transport dir d l (c x) (c y) w hw⟩

/-- Concrete mixed orientations, with distinct nonzero normalizations. -/
theorem mixed_path_fixture :
    WitnessStep .alpha (3 : ℂ) 1 6 2 1 ∧
    WitnessStep .beta (2 : ℂ) 1 3 6 1 ∧
    Transport .alpha (3 : ℂ) 1 6 2 ∧
    Transport .beta (2 : ℂ) 1 3 6 ∧ (3 : ℂ) ≠ 0 := by
  norm_num [WitnessStep, Transport]

/-- The beta component equation can hold vacuously at zero evaluation. -/
theorem beta_zero_witness_counterexample :
    ∃ (d l c c₁ w : ℂ), d ≠ 0 ∧ w = 0 ∧
      (d * l) * (c * w) = c₁ * w ∧ c₁ ≠ d * c * l := by
  refine ⟨1, 0, 1, 1, 0, ?_⟩
  norm_num

/-- The alpha component equation can also hold without its conclusion. -/
theorem alpha_zero_witness_counterexample :
    ∃ (d l c c₁ w : ℂ), w = 0 ∧
      c * w = (d * l * c₁) * w ∧ c ≠ d * l * c₁ := by
  refine ⟨1, 1, 0, 1, 0, ?_⟩
  norm_num

/-- A nonzero component alone cannot supply an inverse for d = 0. -/
theorem beta_no_inverse_counterexample :
    ∃ (d l c c₁ w : ℂ), d = 0 ∧ c * w ≠ 0 ∧
      (d * l) * (c * w) = c₁ * w ∧
      ¬ (∃ u : ℂ, u * d = 1 ∧ c * l = u * c₁) := by
  refine ⟨0, 1, 1, 0, 1, ?_⟩
  norm_num

/-- Vanishing L-factors can destroy nonzero-scalar propagation. -/
theorem zero_l_propagation_counterexample :
    ∃ (d l c c₁ : ℂ), d ≠ 0 ∧ l = 0 ∧ c₁ ≠ 0 ∧
      Transport .alpha d l c c₁ ∧ c = 0 := by
  refine ⟨1, 0, 0, 1, ?_⟩
  norm_num [Transport]

/-- Replacing strict rank decrease by non-increase admits a zero self-loop. -/
theorem invalid_descent_counterexample :
    ∃ (μ : Unit → ℕ) (c : Unit → ℂ),
      (∀ x, μ x = 0 → c x ≠ 0) ∧
      (∀ x, μ x ≠ 0 → ∃ y : Unit,
        μ y ≤ μ x ∧ (1 : ℂ) ≠ 0 ∧ (1 : ℂ) ≠ 0 ∧
        Transport .alpha (1 : ℂ) 1 (c x) (c y)) ∧
      (∃ x, c x = 0) := by
  refine ⟨fun _ => 1, fun _ => 0, ?_, ?_, ⟨(), rfl⟩⟩
  · intro x hx
    norm_num at hx
  · intro x _
    refine ⟨x, le_rfl, ?_⟩
    norm_num [Transport]

end RH26E02

#print axioms RH26E02.beta_normalized_from_component
#print axioms RH26E02.beta_inverse_from_component
#print axioms RH26E02.beta_l_nonzero
#print axioms RH26E02.alpha_from_component
#print axioms RH26E02.alpha_l_nonzero
#print axioms RH26E02.scalar_unique
#print axioms RH26E02.witness_to_transport
#print axioms RH26E02.edge_nonzero
#print axioms RH26E02.rank_descent_nonzero
#print axioms RH26E02.witness_rank_descent_nonzero
#print axioms RH26E02.mixed_path_fixture
#print axioms RH26E02.beta_zero_witness_counterexample
#print axioms RH26E02.alpha_zero_witness_counterexample
#print axioms RH26E02.beta_no_inverse_counterexample
#print axioms RH26E02.zero_l_propagation_counterexample
#print axioms RH26E02.invalid_descent_counterexample

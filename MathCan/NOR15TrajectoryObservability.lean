import Init

/-!
# NOR-15: finite-resolution trajectory observability

A terminal-state decoder cannot uniformly reconstruct an early state on a
pair of examples with a large early-state distance and a small terminal
distance unless the decoder has sufficient Lipschitz sensitivity.

The norm-free argument needs only a triangle inequality, and works for
arbitrary sets of early and late states with Nat-valued distance bounds.
Its purpose is a certified discrete form of the empirical near-pair
trajectory-audit inequality. It DOES NOT establish probabilistic
conditional entropy, mutual information, injectivity of the RRC25 GRU,
or actual closeness/inequality for any floating-point trajectory.
Those premises are supplied by independent numerical evidence.
-/

namespace MathCan.NOR15TrajectoryObservability

universe u v w
variable {Endpoint : Type u} {Early : Type v}

/-- Reconstruction cost for a pair of samples: the total error of one
    terminal decoder for both early states. -/
def pairError (dEarly : Early → Early → Nat)
    (reconstruct : Endpoint → Early)
    (p q : Endpoint) (a b : Early) : Nat :=
  dEarly a (reconstruct p) + dEarly (reconstruct q) b

/-- Geometric separation of two early states is bounded by the decoder
    errors plus its Lipschitz modulus times late-state separation.
    The proof uses only an abstract Nat-valued triangle inequality. -/
theorem trajectory_pair_reconstruction_bound
    (dEarly : Early → Early → Nat)
    (dLate : Endpoint → Endpoint → Nat)
    (reconstruct : Endpoint → Early)
    (L : Nat)
    (triangle : ∀ a b c, dEarly a c ≤ dEarly a b + dEarly b c)
    (lipschitz : ∀ p q,
      dEarly (reconstruct p) (reconstruct q) ≤ L * dLate p q)
    (p q : Endpoint) (a b : Early) :
    dEarly a b ≤ pairError dEarly reconstruct p q a b +
      L * dLate p q := by
  have h1 := triangle a (reconstruct p) b
  have h2 := triangle (reconstruct p) (reconstruct q) b
  have h3 := lipschitz p q
  unfold pairError
  omega

/-- If early-state distance exceeds the budget for two reconstruction
    errors and the decoder's endpoint sensitivity, at least one
    reconstruction error exceeds that budget. -/
theorem near_endpoint_pair_forces_large_error
    (dEarly : Early → Early → Nat)
    (dLate : Endpoint → Endpoint → Nat)
    (reconstruct : Endpoint → Early)
    (L ε : Nat)
    (triangle : ∀ a b c, dEarly a c ≤ dEarly a b + dEarly b c)
    (lipschitz : ∀ p q,
      dEarly (reconstruct p) (reconstruct q) ≤ L * dLate p q)
    (p q : Endpoint) (a b : Early)
    (separation : 2 * ε + L * dLate p q < dEarly a b) :
    ε < dEarly a (reconstruct p) ∨
      ε < dEarly (reconstruct q) b := by
  have h := trajectory_pair_reconstruction_bound
    dEarly dLate reconstruct L triangle lipschitz p q a b
  unfold pairError at h
  by_cases hleft : ε < dEarly a (reconstruct p)
  · exact Or.inl hleft
  · right
    omega

/-- A perfectly matching pair of terminal states cannot support two
    different labels through any terminal-state-only classifier. -/
theorem equal_endpoint_disagreeing_labels_force_error
    {Label : Type w}
    (classifier : Endpoint → Label)
    (p q : Endpoint) (a b : Label)
    (same_endpoint : p = q)
    (different_targets : a ≠ b) :
    classifier p ≠ a ∨ classifier q ≠ b := by
  by_cases ha : classifier p = a
  · right
    intro hb
    apply different_targets
    calc
      a = classifier p := ha.symm
      _ = classifier q := congrArg classifier same_endpoint
      _ = b := hb
  · exact Or.inl ha

/-- A gate that is deterministically computed from the final state may
    be composed into an endpoint-only prediction function. This is the
    exact functional part of the NOR-14 conditional-information limit. -/
theorem endpoint_gate_factors_through_endpoint
    {Gate : Type v} {Prediction : Type w}
    (gate : Endpoint → Gate)
    (predict : Endpoint → Gate → Prediction) :
    ∃ endpointOnly : Endpoint → Prediction,
      ∀ x, endpointOnly x = predict x (gate x) := by
  exact ⟨fun x => predict x (gate x), by intro _; rfl⟩

/-- If all decoder errors are at most epsilon, early-state separation
    cannot exceed twice epsilon plus the Lipschitz transport budget. -/
theorem bounded_errors_force_nearby_early_states
    (dEarly : Early → Early → Nat)
    (dLate : Endpoint → Endpoint → Nat)
    (reconstruct : Endpoint → Early)
    (L ε : Nat)
    (triangle : ∀ a b c, dEarly a c ≤ dEarly a b + dEarly b c)
    (lipschitz : ∀ p q,
      dEarly (reconstruct p) (reconstruct q) ≤ L * dLate p q)
    (p q : Endpoint) (a b : Early)
    (leftError : dEarly a (reconstruct p) ≤ ε)
    (rightError : dEarly (reconstruct q) b ≤ ε) :
    dEarly a b ≤ 2 * ε + L * dLate p q := by
  have h := trajectory_pair_reconstruction_bound
    dEarly dLate reconstruct L triangle lipschitz p q a b
  unfold pairError at h
  omega

#print axioms trajectory_pair_reconstruction_bound
#print axioms near_endpoint_pair_forces_large_error
#print axioms equal_endpoint_disagreeing_labels_force_error
#print axioms endpoint_gate_factors_through_endpoint
#print axioms bounded_errors_force_nearby_early_states

end MathCan.NOR15TrajectoryObservability

import MathCan.GradientStability

/-!
PEF-06: finite coalition memory and exact Boolean noise certificates.
Three independently selected OpenAI math preprints: #119, #127, #132.
The finite latch is not a superquadratic GLOBAL sensitivity witness.
The general all-m formulas remain paper-level with exact Python oracles.
-/

namespace MathCan.CoalitionNoise

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- AND gate on binary positions 2j and 2j+1. -/
def pairGate (w j : Nat) : Nat :=
  ((w / 2^(2*j)) % 2) * ((w / 2^(2*j+1)) % 2)

/-- Parity of three disjoint AND-pair gates. -/
def coalition3 (w : Nat) : Nat :=
  (pairGate w 0 + pairGate w 1 + pairGate w 2) % 2

def coalition2 (w : Nat) : Nat :=
  (pairGate w 0 + pairGate w 1) % 2

theorem no_singleton_changes_zero :
    ∀ i : Fin 6, coalition3 (2^i.val) = coalition3 0 := by
  decide

theorem all_three_disjoint_pair_interventions :
    coalition3 0 = 0 ∧
    coalition3 3 = 1 ∧
    coalition3 12 = 1 ∧
    coalition3 48 = 1 := by
  decide

theorem cross_pair_intervention_is_inactive :
    coalition3 5 = 0 ∧ coalition3 9 = 0 ∧
    coalition3 17 = 0 ∧ coalition3 20 = 0 := by
  decide

/-- A sensitive block contains a complete two-bit AND pair. -/
theorem sensitive_block_contains_complete_pair :
    ∀ w : Fin 64, coalition3 w.val = 1 →
      pairGate w.val 0 = 1 ∨
      pairGate w.val 1 = 1 ∨
      pairGate w.val 2 = 1 := by
  decide

theorem each_complete_pair_changes_at_zero :
    ∀ j : Fin 3, coalition3 (3 * 2^(2*j.val)) = 1 := by
  decide

def weight6 (w : Nat) : Nat :=
  w % 2 + (w / 2) % 2 + (w / 4) % 2 +
  (w / 8) % 2 + (w / 16) % 2 + (w / 32) % 2

def weight4 (w : Nat) : Nat :=
  w % 2 + (w / 2) % 2 + (w / 4) % 2 + (w / 8) % 2

/-- At p=1/4, weighted false alarm numerator is 676/4096=169/1024. -/
def zeroActivationNumerator3 : Nat :=
  ((List.finRange 64).map (fun w : Fin 64 =>
    if coalition3 w.val = 1 then 3^(6-weight6 w.val) else 0)).sum

theorem zeroActivationNumerator3_exact :
    zeroActivationNumerator3 = 676 := by
  decide

/-- Independent four-bit oracle: 30/256=15/128. -/
def zeroActivationNumerator2 : Nat :=
  ((List.finRange 16).map (fun w : Fin 16 =>
    if coalition2 w.val = 1 then 3^(4-weight4 w.val) else 0)).sum

theorem zeroActivationNumerator2_exact :
    zeroActivationNumerator2 = 30 := by
  decide

/-- Sum of singleton pivotal bits over 64 uniform six-bit histories.
    Exact numerator 192, hence average sensitivity 192/64=3. -/
def localSensitivity3 (w : Fin 64) : Nat :=
  ((List.finRange 6).filter (fun i : Fin 6 =>
    coalition3 (Nat.xor w.val (2^i.val)) != coalition3 w.val)).length

def uniformSensitivityNumerator3 : Nat :=
  ((List.finRange 64).map localSensitivity3).sum

theorem uniformSensitivityNumerator3_exact :
    uniformSensitivityNumerator3 = 192 := by
  decide

/-- Two-pair uniform-source noise disagreement under p=1/4:
    1400/(16*256) = 175/512. -/
def uniformNoiseDisagreementNumerator2 : Nat :=
  ((List.finRange 16).map (fun x : Fin 16 =>
    ((List.finRange 16).map (fun z : Fin 16 =>
      if coalition2 (Nat.xor x.val z.val) != coalition2 x.val then
        3^(4-weight4 z.val)
      else 0)).sum)).sum

theorem uniformNoiseDisagreementNumerator2_exact :
    uniformNoiseDisagreementNumerator2 = 1400 := by
  decide

/-- Coefficients 3 p^2 - 6 p^4 + 4 p^6 at p=1/4. -/
theorem mobius_m3_rational_numerator :
    3 * 4^4 - 6 * 4^2 + 4 = (676 : Nat) := by
  decide

theorem zero_singleton_nonzero_coalition_certificate :
    (∀ i : Fin 6, coalition3 (2^i.val) = 0) ∧
    (∀ j : Fin 3, coalition3 (3 * 2^(2*j.val)) = 1) := by
  constructor
  · intro i
    exact (no_singleton_changes_zero i).trans (by decide)
  · exact each_complete_pair_changes_at_zero

#print axioms no_singleton_changes_zero
#print axioms all_three_disjoint_pair_interventions
#print axioms cross_pair_intervention_is_inactive
#print axioms sensitive_block_contains_complete_pair
#print axioms each_complete_pair_changes_at_zero
#print axioms zeroActivationNumerator3_exact
#print axioms zeroActivationNumerator2_exact
#print axioms uniformSensitivityNumerator3_exact
#print axioms uniformNoiseDisagreementNumerator2_exact
#print axioms mobius_m3_rational_numerator
#print axioms zero_singleton_nonzero_coalition_certificate

end MathCan.CoalitionNoise

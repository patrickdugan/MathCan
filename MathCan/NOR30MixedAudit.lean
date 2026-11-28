import MathCan.NOR26PolicyAwareBlindAudit

/-!
# NOR-30: finite minimax audit mixtures and inherited witness coverage

NOR-26 proves the exact uniformly sampled reserve floor for ANY fixed
policy-aware attack selected before challenge coins are revealed.
NOR-30 mixes seven different complete 16-coordinate auditors, with
integer weights on a 16-quantum probability grid. Each arm is sampled
independently of that fixed attack.

If arm i has exact expected hits at least its declared lower bound,
the mixture's weighted expected hits are at least the correspondingly
weighted floors. In particular a positive probability of an authentic
uniform auditor preserves a positive floor, even when deterministic
risk-ranking arms have no such floor.

A two-action/two-attack finite exact witness shows that a randomized
auditor can strictly improve worst-case coverage over every pure
auditor in some games. The empirical question whether mixing beats the
fixed NOR-25 half-reserve policy on NEW RRC25 sources requires the
independent, preregistered NOR-30 experiment.

Theorems are finite exact arithmetic. They assume honest externally
attested target coefficients, an alteration fixed before the actual
audit coins, and sampling independent of the alteration. They neither
establish HMAC security nor certify a learned attack distribution.
-/

namespace MathCan.NOR30MixedAudit

/-- One arm contributes integer grid weight, observed hit count, and
    a certified lower hit count under the selected blind attack. -/
structure AuditArm where
  weight : Nat
  observed : Nat
  lower : Nat

/-- Integer numerator of the expected detection count under an
    externally randomized finite mixture over arms. -/
def weightedObserved : List AuditArm → Nat
  | [] => 0
  | x :: xs => x.weight*x.observed + weightedObserved xs

/-- Weighted mixture of the individual per-arm exact lower bounds. -/
def weightedLower : List AuditArm → Nat
  | [] => 0
  | x :: xs => x.weight*x.lower + weightedLower xs

/-- Pointwise sound lower bounds survive *every* nonnegative finite
    mixture, even when the attacker knows the mixture distribution. -/
theorem any_mixed_policy_inherits_certified_floor
    (arms : List AuditArm)
    (sound : ∀ a ∈ arms, a.lower ≤ a.observed) :
    weightedLower arms ≤ weightedObserved arms := by
  induction arms with
  | nil => simp [weightedLower, weightedObserved]
  | cons a rest ih =>
      have ha : a.lower ≤ a.observed := sound a (by simp)
      have hr : ∀ x ∈ rest, x.lower ≤ x.observed := by
        intro x hx
        exact sound x (by simp [hx])
      have hrestBound := ih hr
      have left := Nat.mul_le_mul_left a.weight ha
      simpa [weightedLower, weightedObserved] using Nat.add_le_add left hrestBound

/-- One positive uniform reserve component forces a strictly positive
    integer lower floor in the mixed score for every finite remainder
    of policies, regardless of their other lower scores. -/
theorem positive_uniform_mass_preserves_positive_floor
    (uniformWeight uniformFloor : Nat)
    (remainder : List AuditArm)
    (hw : 0 < uniformWeight)
    (hf : 0 < uniformFloor) :
    0 < uniformWeight*uniformFloor + weightedLower remainder := by
  have positive : 0 < uniformWeight*uniformFloor :=
    Nat.mul_pos hw hf
  omega

/-- The canonical two-auditor/two-attacker example:
    matched actions detect with score 2, mismatches score 0.
    Pure auditors each admit a zero-detection best response. -/
def crossedPayoff (auditor attacker : Bool) : Nat :=
  if auditor = attacker then 2 else 0

theorem each_pure_policy_has_zero_worstcase
    (auditor : Bool) :
    ∃ attacker : Bool, crossedPayoff auditor attacker = 0 := by
  cases auditor with
  | false => exact ⟨true, rfl⟩
  | true => exact ⟨false, rfl⟩

/-- Mixing the two auditors equally gives numerator 2 against either
    attacker, or expected payoff 1 out of 2, which strictly beats the
    zero worst-case payoff of every pure auditor. -/
theorem equal_mixture_strictly_improves_toy_worstcase
    (attacker : Bool) :
    crossedPayoff false attacker + crossedPayoff true attacker = 2 := by
  cases attacker <;> decide

/-- If the attacker learns the realized auditor before choosing its
    action, the same finite example once again permits zero detection.
    The independent audit-coin timing assumption is essential. -/
theorem seeing_realized_auditor_defeats_toy_mixture
    (auditor : Bool) :
    ∃ attacker : Bool, crossedPayoff auditor attacker = 0 :=
  each_pure_policy_has_zero_worstcase auditor

/-- Adding an arm with zero grid weight cannot change the expected
    score numerator or its inherited certified floor. -/
theorem zero_weight_arm_is_vacuous
    (observed lower : Nat) (rest : List AuditArm) :
    weightedObserved ({weight := 0, observed := observed, lower := lower} :: rest) =
      weightedObserved rest ∧
    weightedLower ({weight := 0, observed := observed, lower := lower} :: rest) =
      weightedLower rest := by
  simp [weightedObserved, weightedLower]

#print axioms any_mixed_policy_inherits_certified_floor
#print axioms positive_uniform_mass_preserves_positive_floor
#print axioms each_pure_policy_has_zero_worstcase
#print axioms equal_mixture_strictly_improves_toy_worstcase
#print axioms seeing_realized_auditor_defeats_toy_mixture
#print axioms zero_weight_arm_is_vacuous

end MathCan.NOR30MixedAudit

import Init

/-!
# NHB-01: exact finite arithmetic for noisy terminal monitors

Companion to Compactification-Theory NHB-01 (#119 x #127 source pair).
The general information-contraction and polynomial-threshold sensitivity
claims are not formalized here. This Init-only module checks the exact
rational-noise numerators and a decoder/threshold separation argument.

At per-step crossover 1/20, the effective crossover is
  noiseNum T / (2*10^T), where noiseNum T = 10^T - 9^T.
With initial target flips 1/10, the balanced-coordinate error is
  targetNum T / 10^(T+1).
-/
namespace MathCan.NoisyHorizon

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def noiseNum : Nat → Nat
  | 0 => 0
  | n + 1 => 9 * noiseNum n + 10 ^ n

theorem noise_numerator_identity (n : Nat) :
    noiseNum n + 9 ^ n = 10 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [noiseNum, Nat.pow_succ]
      omega

def targetNum : Nat → Nat
  | 0 => 1
  | n + 1 => 9 * targetNum n + 5 * 10 ^ n

theorem target_error_numerator_identity (n : Nat) :
    targetNum n + 4 * 9 ^ n = 5 * 10 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [targetNum, Nat.pow_succ]
      omega

/-- This is the cross-multiplied monotonicity of
    targetNum n / 10^(n+1), with positive denominators. -/
theorem target_error_nondecreasing (n : Nat) :
    10 * targetNum n ≤ targetNum (n + 1) := by
  have h := target_error_numerator_identity n
  simp only [targetNum]
  omega

/-- Four noisy steps retain coordinate error at most 1/4. -/
theorem four_steps_meet_quarter_error :
    4 * targetNum 4 ≤ 10 ^ 5 := by
  decide

/-- Five noisy steps exceed error 1/4. -/
theorem five_steps_exceed_quarter_error :
    10 ^ 6 < 4 * targetNum 5 := by
  decide

/-- Numerators used by the separately proved probabilistic envelope. -/
theorem exact_four_five_numerators :
    targetNum 4 = 23756 ∧ targetNum 5 = 263804 := by
  decide

/-- A threshold at the midpoint separates distinct rational levels
    after choosing a common positive denominator. -/
theorem midpoint_separates (a b : Int) (h : a < b) :
    2 * a < a + b ∧ a + b < 2 * b := by
  omega

/-- Any exact query decoder separates inputs requiring opposite answers. -/
theorem different_answers_require_different_codes
    {Source Memory : Type} (encode : Source → Memory)
    (decode : Memory → Bool) {x y : Source}
    (hx : decode (encode x) = true)
    (hy : decode (encode y) = false) : encode x ≠ encode y := by
  intro same
  have contradiction : true = false := by
    calc
      true = decode (encode x) := hx.symm
      _ = decode (encode y) := congrArg decode same
      _ = false := hy
  cases contradiction

/-- The finite majority posterior table has eight levels in the
    separate exact Python certificate; three bits encode eight states. -/
theorem eight_states_need_three_bits :
    (2 : Nat) ^ 2 < 8 ∧ 8 ≤ (2 : Nat) ^ 3 := by
  decide

#print axioms noise_numerator_identity
#print axioms target_error_numerator_identity
#print axioms target_error_nondecreasing
#print axioms four_steps_meet_quarter_error
#print axioms five_steps_exceed_quarter_error
#print axioms exact_four_five_numerators
#print axioms midpoint_separates
#print axioms different_answers_require_different_codes
#print axioms eight_states_need_three_bits

end MathCan.NoisyHorizon

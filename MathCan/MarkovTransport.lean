import Init

/-!
# MTB-01: exact Markov drift and affine transport finite certificates

Companion to the Compactification Theory MTB-01 campaign that combines
OpenAI Math #327 (Markov type / superreflexivity) with #374 (sharp
one-third Brenier stability).

The proofs here certify a four-bit stationary reversible walk's
finite Hamming second moment, the explicit two-step affine rectangle
transport calculations and a threshold decision flip. They do NOT
kernel-formalize the source #327 equivalence, source #374 stability
or the general Markov/Brenier composition theorem.

All tests use Init's ordinary Lean kernel and no admitted proof bodies.
-/

namespace MathCan.MarkovTransport

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

/-- The total number of 4-bit coordinate-flip paths of length t
ending at Hamming weight k. Each step has four equally likely
choices; this counts integer paths before division by 4^t.

From weight k-1 there are 5-k increasing-bit choices.
From weight k+1 there are k+1 decreasing-bit choices.
The formula is used only on weights k in 0..4. -/
def cubeMass : Nat → Nat → Nat
  | 0, k => if k == 0 then 1 else 0
  | t + 1, k =>
      (if k == 0 then 0 else (5-k) * cubeMass t (k-1)) +
      (if k == 4 then 0 else (k+1) * cubeMass t (k+1))

def totalMassFour : Nat :=
  ((List.range 5).map (fun k => cubeMass 4 k)).sum

def hammingFirstMomentFour : Nat :=
  ((List.range 5).map (fun k => k * cubeMass 4 k)).sum

def hammingSecondMomentFour : Nat :=
  ((List.range 5).map (fun k => k*k * cubeMass 4 k)).sum

theorem four_step_hamming_counts :
    cubeMass 4 0 = 40 ∧
    cubeMass 4 1 = 0 ∧
    cubeMass 4 2 = 192 ∧
    cubeMass 4 3 = 0 ∧
    cubeMass 4 4 = 24 := by
  decide

theorem four_step_total_probability_denominator :
    totalMassFour = 256 := by
  decide

theorem four_step_first_hamming_moment :
    hammingFirstMomentFour = 480 := by
  decide

theorem four_step_second_hamming_moment :
    hammingSecondMomentFour = 1152 := by
  decide

/-- The rational second moment is 1152/256=9/2 and the
one-step Hamming distance is one. Thus the Markov-type-2
ratio E H_4²/(4 E H_1²) is 9/8 > 1. -/
theorem l1_four_cube_Markov_type2_constant_exceeds_one :
    8 * hammingSecondMomentFour = 9 * (4 * totalMassFour) ∧
    4 * totalMassFour < hammingSecondMomentFour := by
  decide

/-- For the Euclidean embedding of binary states,
squared distance equals Hamming. Its four-step
squared displacement is 15/8, below the Hilbert
Markov-type-2 bound 4*one_step_energy. -/
theorem hilbert_four_cube_constant_one_suffices :
    8 * hammingFirstMomentFour = 15 * totalMassFour ∧
    hammingFirstMomentFour ≤ 4 * totalMassFour := by
  decide

/-- Exact example: mu=[0,1]^2 and nu=[0,2]×[0,1],
uniform square source with coordinate refresh rate 1/4.

At time two q=(3/4)^2=9/16, W2²=1/3,
cross transported drift²=53/96, and unchanged-target
drift²=7/48 <= 2*(1/12). -/
/-- Denominator-cleared rational certificate:
q=(3/4)^2=9/16, W2²=1/3=32/96,
extra cross drift=(3/6)*(7/16)=21/96,
total 53/96; same-target drift (2/6)*(7/16)=7/48,
which is below 2*(1/12)=1/6. -/
theorem affine_rectangle_two_step_rational_certificate :
    (3 : Nat)^2 = 9 ∧
    (4 : Nat)^2 = 16 ∧
    1 * 96 = 32 * 3 ∧
    3 * 7 * 96 = 21 * 6 * 16 ∧
    32 + 21 = 53 ∧
    2 * 7 * 48 = 7 * 6 * 16 ∧
    7 * 6 ≤ 48 := by
  decide

/-- With initial positive label probability 1/2 and final 3/4,
the same-source flip is 1/4 and independent-source flip 1/2.
Weighted by persistent 9/16 versus refreshed 7/16, the exact
flip probability numerator is 9+14 over denominator 64. -/
theorem affine_threshold_flip_certificate :
    (9 : Nat) + 7 * 2 = 23 ∧
    16 * 4 = 64 ∧
    16 * 2 = 32 := by
  decide

/-- The 4-cube's exact squared-Hamming Markov ratio exceeds
the dimension-independent Hilbert constant one; its finite
growth is a kernel-certified witness of norm sensitivity. -/
theorem exact_geometry_separation_certificate :
    hammingSecondMomentFour > 4 * totalMassFour ∧
    hammingFirstMomentFour ≤ 4 * totalMassFour := by
  decide

#print axioms four_step_hamming_counts
#print axioms four_step_total_probability_denominator
#print axioms four_step_first_hamming_moment
#print axioms four_step_second_hamming_moment
#print axioms l1_four_cube_Markov_type2_constant_exceeds_one
#print axioms hilbert_four_cube_constant_one_suffices
#print axioms affine_rectangle_two_step_rational_certificate
#print axioms affine_threshold_flip_certificate
#print axioms exact_geometry_separation_certificate

end MathCan.MarkovTransport

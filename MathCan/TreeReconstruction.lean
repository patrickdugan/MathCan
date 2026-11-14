import Init

/-!
# KSR-01: exact integer certificates for finite branching moments

This module formalizes finite polynomial arithmetic used by
Compactification-Theory KSR-01, which combines OpenAI Math
families #229 and #236 at the common Kesten-Stigum parameter.

Here q=3, branching b=2, channel lambda=4/5, t=32/25.
For a q-state contrast g_j(s)=3*1{s=j}-1, the unnormalized
symmetric channel has weight 13 on its diagonal and weight
1 on each off-diagonal entry, with denominator 15.
The displayed eigenfunction identity therefore has factor 12,
giving lambda=12/15=4/5.

Define A_L by V_L=A_L/32^L for the leaf-sum
second-moment recurrence V_{L+1}=(25/32)V_L+1/2.
The certificate shows V_L<=16/7 for all finite L.
We also cover independent half retention with normalized
variance (A_L+25^L)/32^L.

Lean verifies the integer channel identities and recurrence
algebra. Probability, optimal posterior accuracy, the infinite
root-reconstruction theorem, and the factor-of-IID source
result are paper-level statements with independent finite
Python checks in Compactification Theory, not Lean theorems here.
-/

namespace MathCan.TreeReconstruction

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Integer channel numerator for q=3 with eigenvalue 4/5:
    diagonal 13, off-diagonal 1, row total 15. -/
def weight (root child : Fin 3) : Int :=
  if root == child then 13 else 1

/-- The signed root-label contrast is 2 at the named state, -1 elsewhere. -/
def contrast (label state : Fin 3) : Int :=
  if label == state then 2 else -1

/-- The kernel-normalization identity for all three possible roots. -/
theorem weights_sum_to_fifteen :
    ∀ root : Fin 3,
      ((List.finRange 3).map (weight root)).sum = 15 := by
  decide

/-- The q=3 contrast is an exact eigenfunction with eigenvalue 12/15. -/
theorem contrast_transfer_eigenvalue :
    ∀ root label : Fin 3,
      ((List.finRange 3).map
        (fun child => weight root child * contrast label child)).sum
          = 12 * contrast label root := by
  decide

/-- A_L is the numerator of V_L with denominator 32^L.
    V_{L+1}=(25/32)*V_L+1/2, V_0=1. -/
def momentNum : Nat → Nat
  | 0 => 1
  | n + 1 => 25 * momentNum n + 16 * 32 ^ n

/-- Exact geometric decay of the gap to the limiting second moment:
    16*32^L - 7*A_L = 9*25^L. -/
theorem moment_gap_identity (n : Nat) :
    7 * momentNum n + 9 * 25 ^ n = 16 * 32 ^ n := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      simp only [momentNum, Nat.pow_succ]
      omega

/-- This cross-multiplied inequality is V_L <= 16/7.
    It in turn certifies the q=3 root-MAP lower bound 5/8
    once the probabilistic reconstruction theorem is supplied. -/
theorem supercritical_second_moment_ceiling (n : Nat) :
    7 * momentNum n ≤ 16 * 32 ^ n := by
  have h := moment_gap_identity n
  omega

/-- With independent retention probability 1/2 the moment
    numerator becomes A_L + 25^L, over 32^L. -/
def halfRetentionNum (n : Nat) : Nat :=
  momentNum n + 25 ^ n

/-- Exact residual half-retention gap to the same limit. -/
theorem half_retention_gap_identity (n : Nat) :
    7 * halfRetentionNum n + 2 * 25 ^ n = 16 * 32 ^ n := by
  have h := moment_gap_identity n
  simp only [halfRetentionNum]
  omega

/-- The half-retained branch remains under V_infty =16/7. -/
theorem half_retention_second_moment_ceiling (n : Nat) :
    7 * halfRetentionNum n ≤ 16 * 32 ^ n := by
  have h := half_retention_gap_identity n
  omega

/-- Critical b=4, lambda=1/2 has t=1 and V_L=(4+3L)/4. -/
def criticalNum (depth : Nat) : Nat :=
  4 + 3 * depth

theorem critical_linear_growth (depth : Nat) :
    criticalNum (depth + 1) = criticalNum depth + 3 := by
  simp [criticalNum]
  omega

theorem critical_depth_eight : criticalNum 8 = 28 := by
  decide

#print axioms weights_sum_to_fifteen
#print axioms contrast_transfer_eigenvalue
#print axioms moment_gap_identity
#print axioms supercritical_second_moment_ceiling
#print axioms half_retention_gap_identity
#print axioms half_retention_second_moment_ceiling
#print axioms critical_linear_growth
#print axioms critical_depth_eight

end MathCan.TreeReconstruction

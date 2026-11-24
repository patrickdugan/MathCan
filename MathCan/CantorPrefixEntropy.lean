import Init

/-!
CLN-01: finite arithmetic core of the conditional prefix-entropy bound.
This file deliberately leaves the analytic theorem and general order
growth to a separate Mathlib-enabled development.
-/
namespace MathCan.CantorPrefixEntropy

/-- Each residue fiber has an injective quotient coordinate. -/
theorem quotient_remainder_injective (n m P : Nat)
    (hq : n / P = m / P) (hr : n % P = m % P) : n = m := by
  have hn := Nat.div_add_mod n P
  have hm := Nat.div_add_mod m P
  rw [hq, hr] at hn
  exact hn.symm.trans hm

/-- If M <= K*P and P*R <= N, the scaled full-period term
is at most K*N. These are explicit arithmetic premises. -/
theorem period_term_bound (M K P R N : Nat)
    (hM : M ≤ K * P) (hR : P * R ≤ N) :
    M * R ≤ K * N := by
  calc
    M * R ≤ (K * P) * R := Nat.mul_le_mul_right R hM
    _ = K * (P * R) := Nat.mul_assoc K P R
    _ ≤ K * N := Nat.mul_le_mul_left K hR

/-- Assemble the collision estimate after clearing normalization.
R stands for floor(N/P), or any upper bound for the quotient term
satisfying the stated scaled inequality. -/
theorem collision_envelope (M N K R : Nat)
    (hM : M ≤ N) (hR : M * R ≤ K * N) :
    M * (N * (1 + R)) ≤ N * (N + K * N) := by
  calc
    M * (N * (1 + R)) = N * (M * (1 + R)) :=
      Nat.mul_left_comm M N (1 + R)
    _ = N * (M + M * R) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ N * (N + K * N) :=
      Nat.mul_le_mul_left N (Nat.add_le_add hM hR)

/-- Finite first-return certificate, with every smaller positive
exponent explicitly ruled out. No general order theorem is assumed. -/
def firstReturnCheck (b M P : Nat) : Bool :=
  (P != 0) && (b ^ P % M == 1) &&
    (List.range P).all (fun n => n == 0 || b ^ n % M != 1)

theorem binary_mod3 : firstReturnCheck 2 3 2 = true := by decide
theorem binary_mod9 : firstReturnCheck 2 9 6 = true := by decide
theorem binary_mod27 : firstReturnCheck 2 27 18 = true := by decide
theorem binary_mod81 : firstReturnCheck 2 81 54 = true := by decide
theorem decimal_mod27 : firstReturnCheck 10 27 3 = true := by decide
theorem decimal_mod81 : firstReturnCheck 10 81 9 = true := by decide
theorem base5_mod36 : firstReturnCheck 5 36 6 = true := by decide
theorem wrong_period_rejected : firstReturnCheck 2 27 9 = false := by decide
theorem multiple_period_rejected : firstReturnCheck 2 9 12 = false := by decide

#print axioms quotient_remainder_injective
#print axioms period_term_bound
#print axioms collision_envelope
#print axioms binary_mod3
#print axioms binary_mod9
#print axioms binary_mod27
#print axioms binary_mod81
#print axioms decimal_mod27
#print axioms decimal_mod81
#print axioms base5_mod36
#print axioms wrong_period_rejected
#print axioms multiple_period_rejected

end MathCan.CantorPrefixEntropy

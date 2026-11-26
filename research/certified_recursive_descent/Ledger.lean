import Std

namespace CRD01

-- Exact finite ledger only, not the asymptotic factoring theorem.
theorem cube_upper : (5000 : Nat)^3 < 2 * 3969^3 := by decide
theorem contraction_upper : (104 : Nat) * 3969 * 100 < 8256 * 5000 := by decide
theorem induction_slack : (2115 : Nat) + 8256 < 10400 := by decide
theorem exact_phase_sum : (2115 : Nat) + 8256 = 10371 := by decide
theorem certificate_slack :
    (2115 : Nat) * 5000 + 10400 * 3969 < 10400 * 5000 := by decide

end CRD01

import Lean

namespace GalacticityEpistemic

/-- With total accepted-clean mass p, the mass of accepted clean paths
    that did not probe coordinate j is bounded by false-admission mass e.
    Hence at least p-e accepted mass probes that coordinate. -/
theorem coordinate_detection (p detected missed e : Nat)
    (split : p = detected + missed) (falseAdmission : missed ≤ e) :
    p - e ≤ detected := by omega

/-- The hard-cap counting inequality, given the aggregate incidence
    bounds: every coordinate detects at least p-e accepted mass, and
    each accepted execution uses at most m probes. -/
theorem audit_cap (N p e m incidence : Nat)
    (lower : N * (p - e) ≤ incidence)
    (upper : incidence ≤ p * m) :
    N * (p - e) ≤ p * m :=
  Nat.le_trans lower upper

theorem audit_equivalence (N p e m : Nat) (hm : m ≤ N) :
    p * (N - m) ≤ e * N ↔ N * (p - e) ≤ p * m := by
  have h₁ : p * (N - m) + p * m = p * N := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hm]
  by_cases h : e ≤ p
  · have h₂ : N * (p - e) + e * N = p * N := by
      rw [Nat.mul_comm e N, ← Nat.mul_add, Nat.sub_add_cancel h, Nat.mul_comm N p]
    omega
  · have h' : p ≤ e := by omega
    have hz : p - e = 0 := Nat.sub_eq_zero_of_le h'
    have he : p * N ≤ e * N := Nat.mul_le_mul_right N h'
    simp [hz]
    omega

/-- Two possible worlds that cannot be distinguished at the point of
    admission cannot support opposite deterministic admission decisions. -/
theorem aliased_admission {W O : Type} (obs : W → O)
    (admit : O → Bool) (good bad : W) (same : obs good = obs bad)
    (accepted : admit (obs good) = true) :
    admit (obs bad) = true := by
  rw [← same]
  exact accepted

/-- Preserve the same prior on both branches. Every prior-specific
    sum is bounded by the sum of independent branch upper bounds. -/
theorem branchwise_upper (a b A B : Nat)
    (ha : a ≤ A) (hb : b ≤ B) : a + b ≤ A + B := by omega

/-- Convex-mixture mass bounds, represented with integer weights. -/
theorem mixture_upper (p q cap a b : Nat)
    (hp : p ≤ cap) (hq : q ≤ cap) :
    a * p + b * q ≤ (a + b) * cap := by
  have h₁ : a * p ≤ a * cap := Nat.mul_le_mul_left a hp
  have h₂ : b * q ≤ b * cap := Nat.mul_le_mul_left b hq
  rw [Nat.add_mul]
  omega

theorem mixture_lower (p q floor a b : Nat)
    (hp : floor ≤ p) (hq : floor ≤ q) :
    (a + b) * floor ≤ a * p + b * q := by
  have h₁ : a * floor ≤ a * p := Nat.mul_le_mul_left a hp
  have h₂ : b * floor ≤ b * q := Nat.mul_le_mul_left b hq
  rw [Nat.add_mul]
  omega

/-- An event bound in total variation implies a conservative risk cap. -/
theorem tv_admission (nominal actual radius cap : Nat)
    (distance : actual ≤ nominal + radius)
    (reserve : nominal + radius ≤ cap) : actual ≤ cap :=
  Nat.le_trans distance reserve

end GalacticityEpistemic

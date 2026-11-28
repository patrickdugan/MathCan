import Init

/-!
# RHD-13: finite unit-character obstruction certificates

These Init-only theorems exclude nonzero F_p-linear functionals that
vanish on both given local first-layer unit logarithm vectors.
The vectors are separately computed and checked by Python in RHD-10C
and RHD-11. These theorems do not construct global number-field units,
local characters, or an automorphic representation.
-/

namespace MathCan.RHFiniteUnitObstructions

def Kills (p a b u v : Nat) : Prop :=
  (a * u + b * v) % p = 0

/-- Q(zeta_24), p=5: local factor 0, units 1-zeta and 1-zeta^7. -/
theorem zeta24_factor0 :
    ∀ a b : Fin 5,
      Kills 5 a.val b.val 3 0 →
      Kills 5 a.val b.val 4 4 →
      a = 0 ∧ b = 0 := by
  intro a b h₁ h₂
  unfold Kills at h₁ h₂
  constructor <;> apply Fin.ext <;> omega

theorem zeta24_factor1 :
    ∀ a b : Fin 5,
      Kills 5 a.val b.val 4 2 →
      Kills 5 a.val b.val 3 0 →
      a = 0 ∧ b = 0 := by
  intro a b h₁ h₂
  unfold Kills at h₁ h₂
  constructor <;> apply Fin.ext <;> omega

theorem zeta24_factor2 :
    ∀ a b : Fin 5,
      Kills 5 a.val b.val 3 0 →
      Kills 5 a.val b.val 0 2 →
      a = 0 ∧ b = 0 := by
  intro a b h₁ h₂
  unfold Kills at h₁ h₂
  constructor <;> apply Fin.ext <;> omega

theorem zeta24_factor3 :
    ∀ a b : Fin 5,
      Kills 5 a.val b.val 0 4 →
      Kills 5 a.val b.val 3 0 →
      a = 0 ∧ b = 0 := by
  intro a b h₁ h₂
  unfold Kills at h₁ h₂
  constructor <;> apply Fin.ext <;> omega

/-- Q(zeta_20), p=29, vector evidence from RHD-10C. -/
theorem zeta20_factor0 :
    ∀ a b : Fin 29,
      Kills 29 a.val b.val 13 14 →
      Kills 29 a.val b.val 0 28 →
      a = 0 ∧ b = 0 := by
  intro a b h₁ h₂
  unfold Kills at h₁ h₂
  constructor <;> apply Fin.ext <;> omega

theorem zeta20_factor1 :
    ∀ a b : Fin 29,
      Kills 29 a.val b.val 17 23 →
      Kills 29 a.val b.val 20 3 →
      a = 0 ∧ b = 0 := by
  intro a b h₁ h₂
  unfold Kills at h₁ h₂
  constructor <;> apply Fin.ext <;> omega

theorem zeta20_factor2 :
    ∀ a b : Fin 29,
      Kills 29 a.val b.val 14 23 →
      Kills 29 a.val b.val 7 3 →
      a = 0 ∧ b = 0 := by
  intro a b h₁ h₂
  unfold Kills at h₁ h₂
  constructor <;> apply Fin.ext <;> omega

theorem zeta20_factor3 :
    ∀ a b : Fin 29,
      Kills 29 a.val b.val 14 14 →
      Kills 29 a.val b.val 2 28 →
      a = 0 ∧ b = 0 := by
  intro a b h₁ h₂
  unfold Kills at h₁ h₂
  constructor <;> apply Fin.ext <;> omega

#print axioms zeta24_factor0
#print axioms zeta24_factor1
#print axioms zeta24_factor2
#print axioms zeta24_factor3
#print axioms zeta20_factor0
#print axioms zeta20_factor1
#print axioms zeta20_factor2
#print axioms zeta20_factor3

end MathCan.RHFiniteUnitObstructions

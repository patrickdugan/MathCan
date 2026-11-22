import Init

/-!
# RHD-14: conjugation-invariant first-layer norm character

Closed modular arithmetic for the conjugation pairs in Q(zeta_20) at 29
and Q(zeta_24) at 5. Each identity says that transporting the local
first-layer coordinates under zeta ↦ zeta^{-1} preserves the exponent
of a character pulled back from the rational norm.

This does not define UA E 1, local completions, Hecke characters,
or the original automorphic TyEll predicate.
-/

namespace MathCan.RHNormOneCollapse

/-- A norm-pulled character with normalized value at 1 vanishes on
every input in the kernel of the supplied norm map. -/
theorem norm_pullback_trivial_on_kernel {G : Type} (norm : G → Int)
    (character : Int → Int) (hchi : character 1 = 0)
    (g : G) (h : norm g = 1) : character (norm g) = 0 := by
  simpa [h] using hchi

/-- Conjugation pairs the four p=29 lifted factors by their opposite
quadratic coefficient c, preserving the first-layer rational trace. -/
theorem zeta20_factor0_to3 (a b : Nat) :
    (2*a + 27*b) % 29 =
      (2*(a + 27*b) + 2*b) % 29 := by omega

theorem zeta20_factor3_to0 (a b : Nat) :
    (2*a + 2*b) % 29 =
      (2*(a + 2*b) + 27*b) % 29 := by omega

theorem zeta20_factor1_to2 (a b : Nat) :
    (2*a + 15*b) % 29 =
      (2*(a + 15*b) + 14*b) % 29 := by omega

theorem zeta20_factor2_to1 (a b : Nat) :
    (2*a + 14*b) % 29 =
      (2*(a + 14*b) + 15*b) % 29 := by omega

/-- The same phenomenon at Q(zeta_24), p=5. -/
theorem zeta24_factor0_to3 (a b : Nat) :
    (2*a + 4*b) % 5 =
      (2*(a + 4*b) + b) % 5 := by omega

theorem zeta24_factor3_to0 (a b : Nat) :
    (2*a + b) % 5 =
      (2*(a + b) + 4*b) % 5 := by omega

theorem zeta24_factor1_to2 (a b : Nat) :
    (2*a + 3*b) % 5 =
      (2*(a + 3*b) + 2*b) % 5 := by omega

theorem zeta24_factor2_to1 (a b : Nat) :
    (2*a + 2*b) % 5 =
      (2*(a + 2*b) + 3*b) % 5 := by omega

#print axioms norm_pullback_trivial_on_kernel
#print axioms zeta20_factor0_to3
#print axioms zeta20_factor3_to0
#print axioms zeta20_factor1_to2
#print axioms zeta20_factor2_to1
#print axioms zeta24_factor0_to3
#print axioms zeta24_factor3_to0
#print axioms zeta24_factor1_to2
#print axioms zeta24_factor2_to1

end MathCan.RHNormOneCollapse

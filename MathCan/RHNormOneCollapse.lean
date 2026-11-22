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

/-- For Q(zeta_24), p=5 the reciprocal-factor involution is
(0 2)(1 3), with a nontrivial alpha coefficient under inversion. -/
theorem zeta24_factor0_to2 (a b : Nat) :
    (2*a + 4*b) % 5 =
      (2*(a + 4*b) + 2*(3*b)) % 5 := by omega

theorem zeta24_factor2_to0 (a b : Nat) :
    (2*a + 2*b) % 5 =
      (2*(a + 2*b) + 4*(2*b)) % 5 := by omega

theorem zeta24_factor1_to3 (a b : Nat) :
    (2*a + 3*b) % 5 =
      (2*(a + 3*b) + 2*b) % 5 := by omega

theorem zeta24_factor3_to1 (a b : Nat) :
    (2*a + b) % 5 =
      (2*(a + b) + 3*(3*b)) % 5 := by omega

#print axioms norm_pullback_trivial_on_kernel
#print axioms zeta20_factor0_to3
#print axioms zeta20_factor3_to0
#print axioms zeta20_factor1_to2
#print axioms zeta20_factor2_to1
#print axioms zeta24_factor0_to2
#print axioms zeta24_factor2_to0
#print axioms zeta24_factor1_to3
#print axioms zeta24_factor3_to1

/-- A 29-torsion exponent that annihilates every 20th root is zero.
This finite relation models compatibility with μ20, not actual U(1) units. -/
theorem zeta20_root_torsion_compatible (a : Fin 29)
    (h : (20*a.val) % 29 = 0) : a = 0 := by
  apply Fin.ext
  omega

/-- The corresponding order-5 character and μ24 finite relation. -/
theorem zeta24_root_torsion_compatible (a : Fin 5)
    (h : (24*a.val) % 5 = 0) : a = 0 := by
  apply Fin.ext
  omega

#print axioms zeta20_root_torsion_compatible
#print axioms zeta24_root_torsion_compatible

end MathCan.RHNormOneCollapse

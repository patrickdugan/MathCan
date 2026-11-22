import Init
import MathCan.RHPrimeFibers

/-!
# RHD-15: local split U(1) torus character first-layer certificates

We model the split E/F local norm-one relation as (u,bar(u)^-1).
The finite coefficient pair at the conjugate prime is the negative
of the reciprocal-factor transport. This supplies an asymmetric
nontrivial local exponent while the absolute norm exponent vanishes.

These Init-only equalities do not construct the original UA E 1,
IsAutRepU, RU, TyEll, SatU, or an adelic torus character.
-/

namespace MathCan.RHSplitTorusCharacter

/-- Conjugation for Q(zeta20), p29: (0 3)(1 2).
The paired local exponents cancel modulo 29. -/
theorem pair29_0 (a b : Int) :
    ((2*a - 2*b) + (2*(-a - 27*b) - 27*(-b))) % 29 = 0 := by omega

theorem pair29_1 (a b : Int) :
    ((2*a - 14*b) + (2*(-a - 15*b) - 15*(-b))) % 29 = 0 := by omega

theorem pair29_2 (a b : Int) :
    ((2*a - 15*b) + (2*(-a - 14*b) - 14*(-b))) % 29 = 0 := by omega

theorem pair29_3 (a b : Int) :
    ((2*a - 27*b) + (2*(-a - 2*b) - 2*(-b))) % 29 = 0 := by omega

/-- Q(zeta24), p5: reciprocal quadratic pairs (0 2)(1 3).
The quadratic constants modulo 5 are d=(2,3,3,2). -/
theorem pair5_0 (a b : Int) :
    ((2*a - b) + (2*(-a + 2*3*b) - 3*(2*b))) % 5 = 0 := by omega

theorem pair5_1 (a b : Int) :
    ((2*a - 2*b) + (2*(-a + 3*4*b) - 4*(3*b))) % 5 = 0 := by omega

theorem pair5_2 (a b : Int) :
    ((2*a - 3*b) + (2*(-a + 3*b) - (3*b))) % 5 = 0 := by omega

theorem pair5_3 (a b : Int) :
    ((2*a - 4*b) + (2*(-a + 4*b) - 2*(2*b))) % 5 = 0 := by omega

/-- The selected-component trace has an explicit preimage for every
order-29 exponent; multiplication by 2 has inverse 15 modulo 29. -/
theorem selected_character_surjective29 (t : Fin 29) :
    ∃ a : Fin 29, (2*a.val) % 29 = t.val := by
  refine ⟨⟨(15*t.val) % 29, by omega⟩, ?_⟩
  have ht := t.isLt
  dsimp
  omega

/-- Multiplication by 2 has inverse 3 modulo 5. -/
theorem selected_character_surjective5 (t : Fin 5) :
    ∃ a : Fin 5, (2*a.val) % 5 = t.val := by
  refine ⟨⟨(3*t.val) % 5, by omega⟩, ?_⟩
  have ht := t.isLt
  dsimp
  omega

/-- The real-place tag of a source factor in Q(zeta20).
Finite labels are a shadow of contraction to O_(E^+). -/
def real29 (j : Nat) : Nat :=
  if j = 0 ∨ j = 3 then 0 else 1

def mate29 (j : Nat) : Nat := 3-j

theorem conjugate_same_real29 (j : Fin 4) :
    real29 j.val = real29 (mate29 j.val) := by
  rcases j with ⟨n, hn⟩
  have h : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases h with h | h | h | h <;> subst n <;> simp [real29, mate29]

def real5 (j : Nat) : Nat :=
  if j = 0 ∨ j = 2 then 0 else 1

def mate5 (j : Nat) : Nat :=
  if j = 0 then 2 else if j = 1 then 3 else if j = 2 then 0 else 1

theorem conjugate_same_real5 (j : Fin 4) :
    real5 j.val = real5 (mate5 j.val) := by
  rcases j with ⟨n, hn⟩
  have h : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases h with h | h | h | h <;> subst n <;> simp [real5, mate5]

/-- Nontriviality witnesses for an asymmetric local character. -/
theorem local_witness29 : (2*15) % 29 = 1 := by decide
theorem local_witness5 : (2*3) % 5 = 1 := by decide

/-- Independent quadratic residue ring at p=5 with α²+cα+d=0.
The two sets of coordinates represent the local Hensel factors mod 5. -/
abbrev Residue5 := Int × Int

def multiply5 (d c : Int) (x y : Residue5) : Residue5 :=
  (((x.1*y.1 - d*x.2*y.2) % 5),
   ((x.1*y.2 + x.2*y.1 - c*x.2*y.2) % 5))

def alphaPower5 (d c : Int) : Nat → Residue5
  | 0 => (1, 0)
  | n + 1 => multiply5 d c (alphaPower5 d c n) (0, 1)

/-- In Q(zeta24), ζ^6=i reduces to 2 or 3 in the F5 residue fields.
Factors 0 and 3 share one Q(i) contraction; 1 and 2 share the other. -/
theorem zeta24_quadratic_subfield_tags :
    alphaPower5 2 1 6 = (2, 0) ∧
    alphaPower5 3 2 6 = (3, 0) ∧
    alphaPower5 3 3 6 = (3, 0) ∧
    alphaPower5 2 4 6 = (2, 0) := by decide

/-- The Q(i)-equal prime indices are separated by the E^+ partition. -/
theorem transverse_oneK_apart_shadow5 :
    (alphaPower5 2 1 6).1 = (alphaPower5 2 4 6).1 ∧
    real5 0 ≠ real5 3 ∧
    (alphaPower5 3 2 6).1 = (alphaPower5 3 3 6).1 ∧
    real5 1 ≠ real5 2 := by decide

/-- RHD-12 already computes ζ20^5=i for the four finite residues.
Its Q(i)-equal pairs are different maximal-real-field pairs. -/
theorem transverse_oneK_apart_shadow29 :
    MathCan.RHPrimeFibers.contractionTag MathCan.RHPrimeFibers.w0 =
      MathCan.RHPrimeFibers.contractionTag MathCan.RHPrimeFibers.w2 ∧
    real29 MathCan.RHPrimeFibers.w0.val ≠
      real29 MathCan.RHPrimeFibers.w2.val ∧
    MathCan.RHPrimeFibers.contractionTag MathCan.RHPrimeFibers.w1 =
      MathCan.RHPrimeFibers.contractionTag MathCan.RHPrimeFibers.w3 ∧
    real29 MathCan.RHPrimeFibers.w1.val ≠
      real29 MathCan.RHPrimeFibers.w3.val := by decide

#print axioms zeta24_quadratic_subfield_tags
#print axioms transverse_oneK_apart_shadow5
#print axioms transverse_oneK_apart_shadow29

#print axioms pair29_0
#print axioms pair29_1
#print axioms pair29_2
#print axioms pair29_3
#print axioms pair5_0
#print axioms pair5_1
#print axioms pair5_2
#print axioms pair5_3
#print axioms selected_character_surjective29
#print axioms selected_character_surjective5
#print axioms conjugate_same_real29
#print axioms conjugate_same_real5
#print axioms local_witness29
#print axioms local_witness5

end MathCan.RHSplitTorusCharacter

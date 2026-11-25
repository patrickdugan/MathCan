import Init

/-!
# TRR-03: a five-point quadratic decoder witness

This file checks a single explicit table over the integers modulo 11. The
four finite points lie on y^2 = x^3 + 2*x + 9. Index zero denotes the point
at infinity for the addition table; its decoder coordinates (9, 0) are a
separate sentinel and do not satisfy the affine curve equation.

Closed finite decisions below are reduced by Lean's kernel. No general
theorem about fields, elliptic curves, polynomial degree, or matrix rank
is imported or claimed by these checks.
-/

namespace MathCan.TranslationPolynomialDecoder

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

def xValue (i : Fin 5) : Nat :=
  match i.val with
  | 0 => 9
  | 1 => 4
  | 2 => 8
  | 3 => 8
  | _ => 4

def yValue (i : Fin 5) : Nat :=
  match i.val with
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 8
  | _ => 9

def addIndex (i j : Fin 5) : Fin 5 :=
  ⟨(i.val + j.val) % 5, Nat.mod_lt _ (by decide)⟩

def decoder (u v : Nat × Nat) : Nat :=
  (5*u.1*v.1 + 4*u.2*v.2) % 11

/-- All 25 entries of the translation table have this bilinear decoder. -/
theorem decoder_table :
    ∀ i j : Fin 5,
      xValue (addIndex i j) =
        decoder (xValue i, yValue i) (xValue j, yValue j) := by
  decide

/-- The four ordinary points satisfy the affine equation over F_11. -/
theorem finite_points_on_curve :
    ∀ i : Fin 5, i.val ≠ 0 →
      (yValue i)^2 % 11 = ((xValue i)^3 + 2*xValue i + 9) % 11 := by
  decide

/-- The assigned value at infinity is deliberately outside the affine curve. -/
theorem sentinel_off_curve :
    (yValue 0)^2 % 11 ≠ ((xValue 0)^3 + 2*xValue 0 + 9) % 11 := by
  decide

def addMod (a b : Nat) : Nat := (a+b) % 11
def mulMod (a b : Nat) : Nat := (a*b) % 11
def subMod (a b : Nat) : Nat := (a+11-(b % 11)) % 11
def inverseMod (a : Nat) : Nat := a^9 % 11

/-- `none` represents infinity; `some (x,y)` represents an affine point. -/
abbrev Point := Option (Nat × Nat)

def point (i : Fin 5) : Point :=
  if i.val = 0 then none else some (xValue i, yValue i)

/-- The usual short Weierstrass formulas, specialized to the coefficient 2
    and evaluated modulo 11. This definition is only asserted to agree
    with the five-point table checked below. -/
def addPoint : Point → Point → Point
  | none, q => q
  | p, none => p
  | some (x,y), some (u,v) =>
      if x = u ∧ addMod y v = 0 then none
      else
        let slope :=
          if x = u then
            mulMod (addMod (mulMod 3 (mulMod x x)) 2)
              (inverseMod (mulMod 2 y))
          else
            mulMod (subMod v y) (inverseMod (subMod u x))
        let xNext := subMod (subMod (mulMod slope slope) x) u
        let yNext := subMod (mulMod slope (subMod x xNext)) y
        some (xNext, yNext)

/-- All 25 additions agree with addition of indices modulo five. -/
theorem addition_table :
    ∀ i j : Fin 5, addPoint (point i) (point j) = point (addIndex i j) := by
  decide

/-- All nonzero residues used by the formulas have the claimed inverse. -/
theorem inverse_table :
    ∀ a : Fin 11, a.val ≠ 0 → mulMod a.val (inverseMod a.val) = 1 := by
  decide

/-- The translation minor with rows and columns 0,1 has determinant 1.
    This numerical certificate supports the separate written rank proof. -/
theorem translation_minor_is_one :
    subMod (mulMod (xValue 0) (xValue 2))
      (mulMod (xValue 1) (xValue 1)) = 1 := by
  decide

#print axioms decoder_table
#print axioms finite_points_on_curve
#print axioms sentinel_off_curve
#print axioms addition_table
#print axioms inverse_table
#print axioms translation_minor_is_one

end MathCan.TranslationPolynomialDecoder

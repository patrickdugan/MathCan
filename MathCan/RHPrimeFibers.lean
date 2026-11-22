import Init

/-!
# RHD-12: exact residue factor and quadratic-subfield fiber certificates

This is an Init-only finite arithmetic shadow of proposed height-one prime
ideals of O_{Q(zeta_20)} above 29. It checks the four irreducible residue
factors and the contractions obtained by restricting zeta_20^5 = i.

It does NOT define actual HeightOneSpectrum points or prove upstream OneK,
Apart, SatU, or TyEll. Those steps require the pinned upstream Mathlib field.
-/

namespace MathCan.RHPrimeFibers

/-- Multiplication on coefficient pairs a+b*alpha modulo 29, subject to
alpha²+c alpha-1=0. Equality in this ring is represented by canonical
remainder pairs, so these closed certificates are kernel-reducible. -/
abbrev Residue := Int × Int

def multiply (c : Int) (x y : Residue) : Residue :=
  (((x.1 * y.1 + x.2 * y.2) % 29),
   ((x.1 * y.2 + x.2 * y.1 - c * x.2 * y.2) % 29))

/-- Compute alpha^n in the fixed residue quotient. -/
def alphaPower (c : Int) (n : Nat) : Residue :=
  n.repeat (fun x => multiply c x (0, 1)) (1, 0)

/-- Exact closed irreducibility test for X²+cX-1 over F_29. -/
def hasResidueRoot (c : Int) : Bool :=
  (List.range 29).any fun n =>
    (((Int.ofNat n * Int.ofNat n + c * Int.ofNat n - 1) % 29) == 0)

/-- Four degree-two factors (the residue factors of Phi_20 mod 29) have
no root in F_29. This is a finite computational lemma, not a number field
ideal-primeness proof. -/
theorem four_residue_quadratics_have_no_roots :
    hasResidueRoot 2 = false ∧
    hasResidueRoot 14 = false ∧
    hasResidueRoot (-14) = false ∧
    hasResidueRoot (-2) = false := by
  decide

/-- In the four quadratic residue quotients, alpha^5 is a scalar
respectively 17,12,17,12. Both 17 and 12 square to -1 mod 29. -/
theorem fifth_power_contraction_values :
    alphaPower 2 5 = (17, 0) ∧
    alphaPower 14 5 = (12, 0) ∧
    alphaPower (-14) 5 = (17, 0) ∧
    alphaPower (-2) 5 = (12, 0) := by
  decide

theorem quadratic_subfield_root_checks :
    ((17 * 17 + 1 : Int) % 29 = 0) ∧
    ((12 * 12 + 1 : Int) % 29 = 0) ∧
    (17 : Int) ≠ 12 := by
  decide

/-- The four candidate residue factor indices. -/
def w0 : Fin 4 := ⟨0, by decide⟩
def w1 : Fin 4 := ⟨1, by decide⟩
def w2 : Fin 4 := ⟨2, by decide⟩
def w3 : Fin 4 := ⟨3, by decide⟩

def residueFactorCoefficient (j : Fin 4) : Int :=
  match j.val with
  | 0 => 2
  | 1 => 14
  | 2 => -14
  | _ => -2

/-- Scalar residue of zeta_20^5 in a candidate prime fiber. -/
def contractionTag (j : Fin 4) : Int :=
  (alphaPower (residueFactorCoefficient j) 5).1

theorem two_finite_contraction_fibers :
    contractionTag w0 = 17 ∧ contractionTag w2 = 17 ∧
    contractionTag w1 = 12 ∧ contractionTag w3 = 12 ∧
    w0 ≠ w2 ∧ w1 ≠ w3 ∧
    residueFactorCoefficient w0 ≠ residueFactorCoefficient w2 ∧
    residueFactorCoefficient w1 ≠ residueFactorCoefficient w3 := by
  decide

/-- Unlike a bare combinatorial labeling, these equalities compute
contraction tags from multiplication in the degree-two quotient. -/
theorem two_pairs_share_quadratic_subfield_residues :
    contractionTag w0 = contractionTag w2 ∧
    contractionTag w1 = contractionTag w3 ∧
    contractionTag w0 ≠ contractionTag w1 := by
  decide

#print axioms four_residue_quadratics_have_no_roots
#print axioms fifth_power_contraction_values
#print axioms quadratic_subfield_root_checks
#print axioms two_finite_contraction_fibers
#print axioms two_pairs_share_quadratic_subfield_residues

end MathCan.RHPrimeFibers

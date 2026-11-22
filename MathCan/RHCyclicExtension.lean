import Init
import MathCan.RHNormOneCollapse

/-!
# RHD-16: finite character-extension order inflation

The local norm-one-torus construction in RHD-15 prescribes a character
of order p on a finite cyclic subgroup. A global extension may need
characters of order p^2. The toy group here is G = Z/(p^2), with
H = p*G. A character of H with exponent t in Z/p is represented by
the image of p in a group of p-th roots of unity.

The statement Extends p e t models the extension with generator exponent
e among p^2-th roots. Its necessity and existence are checked below for
p=5 and p=29. This is an exact finite group calculation, not a proof
that a Hecke or automorphic character of U(1) exists.
-/

namespace MathCan.RHCyclicExtension

def Extends (p e t : Nat) : Prop :=
  (p * e) % (p * p) = p * t

/-- An extension with a p^2-th root on the ambient generator restricts
to the desired p-th root precisely when e=t mod p. -/
theorem extension_iff_residue5 (e : Fin 25) (t : Fin 5) :
    Extends 5 e.val t.val ↔ e.val % 5 = t.val := by
  unfold Extends
  have he := e.isLt
  have ht := t.isLt
  omega

theorem extension_iff_residue29 (e : Fin 841) (t : Fin 29) :
    Extends 29 e.val t.val ↔ e.val % 29 = t.val := by
  unfold Extends
  have he := e.isLt
  have ht := t.isLt
  omega

/-- Every prescribed local p-torsion exponent has a p^2-root lift. -/
theorem exists_extension5 (t : Fin 5) :
    ∃ e : Fin 25, Extends 5 e.val t.val := by
  refine ⟨⟨t.val, by have h := t.isLt; omega⟩, ?_⟩
  unfold Extends
  have h := t.isLt
  omega

theorem exists_extension29 (t : Fin 29) :
    ∃ e : Fin 841, Extends 29 e.val t.val := by
  refine ⟨⟨t.val, by have h := t.isLt; omega⟩, ?_⟩
  unfold Extends
  have h := t.isLt
  omega

/-- A character G -> mu_p sends p times a generator to identity.
It cannot extend a local character with nonzero p-torsion exponent. -/
theorem no_mu5_extension_of_nontrivial (a : Fin 5) (t : Fin 5)
    (ht : t ≠ 0) : ¬ Extends 5 (5 * a.val) t.val := by
  unfold Extends
  have ha := a.isLt
  have hb := t.isLt
  intro h
  apply ht
  apply Fin.ext
  omega

theorem no_mu29_extension_of_nontrivial (a : Fin 29) (t : Fin 29)
    (ht : t ≠ 0) : ¬ Extends 29 (29 * a.val) t.val := by
  unfold Extends
  have ha := a.isLt
  have hb := t.isLt
  intro h
  apply ht
  apply Fin.ext
  omega

/-- For local exponent 1, every permissible ambient generator exponent
is prime to p, hence its global order is p^2 in the cyclic model. -/
theorem extension29_primitive (e : Fin 841)
    (h : Extends 29 e.val 1) : e.val % 29 = 1 := by
  exact (extension_iff_residue29 e ⟨1, by decide⟩).mp h

theorem extension5_primitive (e : Fin 25)
    (h : Extends 5 e.val 1) : e.val % 5 = 1 := by
  exact (extension_iff_residue5 e ⟨1, by decide⟩).mp h

/-- The finite cyclotomic root-of-unity compatibility constraints
already established in RHD-14 apply to each local p-primary character. -/
theorem torsion20_compatible (a : Fin 29)
    (h : (20 * a.val) % 29 = 0) : a = 0 :=
  MathCan.RHNormOneCollapse.zeta20_root_torsion_compatible a h

theorem torsion24_compatible (a : Fin 5)
    (h : (24 * a.val) % 5 = 0) : a = 0 :=
  MathCan.RHNormOneCollapse.zeta24_root_torsion_compatible a h

#print axioms extension_iff_residue5
#print axioms extension_iff_residue29
#print axioms exists_extension5
#print axioms exists_extension29
#print axioms no_mu5_extension_of_nontrivial
#print axioms no_mu29_extension_of_nontrivial
#print axioms extension29_primitive
#print axioms extension5_primitive
#print axioms torsion20_compatible
#print axioms torsion24_compatible

end MathCan.RHCyclicExtension

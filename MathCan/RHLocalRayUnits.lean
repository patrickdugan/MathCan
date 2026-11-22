import Init

/-!
# RHD-17: finite local ray-unit quotient certificates

Let R=O_(E_w)/p² in the two unramified quadratic examples.
The local units have p²(p²-1) elements, and the cyclotomic
torsion subgroup μ_n injects into Rˣ. A norm-pulled order-p character
kills μ_n and therefore descends to the quotient. Python separately
checks the complete character distribution and all eight α-orders.

The Lean theorems below are closed finite arithmetic and an abstract
root-orbit invariance lemma. They do not construct R as a Lean
finite ring, the genuine adelic torus or its automorphic character.
-/

namespace MathCan.RHLocalRayUnits

abbrev Pair := Int × Int

/-- Multiplication in (Z/m)[α]/(α²+cα+d). -/
def mul (m : Nat) (d c : Int) (x y : Pair) : Pair :=
  (((x.1*y.1-d*x.2*y.2) % m),
   ((x.1*y.2+x.2*y.1-c*x.2*y.2) % m))

def alphaPow (m : Nat) (d c : Int) : Nat → Pair
  | 0 => (1, 0)
  | n + 1 => mul m d c (alphaPow m d c n) (0, 1)

/-- All four Hensel factors over 29 retain a primitive 20th root. -/
theorem primitive20_factor0 :
    alphaPow 841 840 785 20 = (1, 0) ∧
    alphaPow 841 840 785 10 ≠ (1, 0) ∧
    alphaPow 841 840 785 4 ≠ (1, 0) := by decide

theorem primitive20_factor1 :
    alphaPow 841 840 826 20 = (1, 0) ∧
    alphaPow 841 840 826 10 ≠ (1, 0) ∧
    alphaPow 841 840 826 4 ≠ (1, 0) := by decide

theorem primitive20_factor2 :
    alphaPow 841 840 15 20 = (1, 0) ∧
    alphaPow 841 840 15 10 ≠ (1, 0) ∧
    alphaPow 841 840 15 4 ≠ (1, 0) := by decide

theorem primitive20_factor3 :
    alphaPow 841 840 56 20 = (1, 0) ∧
    alphaPow 841 840 56 10 ≠ (1, 0) ∧
    alphaPow 841 840 56 4 ≠ (1, 0) := by decide

/-- Q(zeta24), p=5: each Hensel factor retains a primitive 24th root. -/
theorem primitive24_factor0 :
    alphaPow 25 7 11 24 = (1, 0) ∧
    alphaPow 25 7 11 12 ≠ (1, 0) ∧
    alphaPow 25 7 11 8 ≠ (1, 0) := by decide

theorem primitive24_factor1 :
    alphaPow 25 18 2 24 = (1, 0) ∧
    alphaPow 25 18 2 12 ≠ (1, 0) ∧
    alphaPow 25 18 2 8 ≠ (1, 0) := by decide

theorem primitive24_factor2 :
    alphaPow 25 18 23 24 = (1, 0) ∧
    alphaPow 25 18 23 12 ≠ (1, 0) ∧
    alphaPow 25 18 23 8 ≠ (1, 0) := by decide

theorem primitive24_factor3 :
    alphaPow 25 7 14 24 = (1, 0) ∧
    alphaPow 25 7 14 12 ≠ (1, 0) ∧
    alphaPow 25 7 14 8 ≠ (1, 0) := by decide

/-- Right multiplication by a chosen torsion root; this is
the orbit-level algebra needed before descending through μ_n. -/
def rightRootOrbit {G : Type} (f : G → G → G) (root : G)
    (x : G) : Nat → G
  | 0 => x
  | n + 1 => f (rightRootOrbit f root x n) root

/-- A character invariant under multiplication by a generator remains
invariant on its entire cyclic orbit. This is an abstract descent lemma. -/
theorem character_constant_on_root_orbits
    {G : Type} (f : G → G → G) (root : G)
    (char : G → Nat) (p : Nat)
    (h : ∀ x, char (f x root) % p = char x % p)
    (x : G) (n : Nat) :
    char (rightRootOrbit f root x n) % p = char x % p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        char (rightRootOrbit f root x (n+1)) % p =
          char (f (rightRootOrbit f root x n) root) % p := rfl
        _ = char (rightRootOrbit f root x n) % p := h _
        _ = char x % p := ih

/-- Exact sizes of the residue-unit groups and quotient by μ20 or μ24. -/
theorem ray_quotient_sizes29 :
    841 * 840 = 706440 ∧
    706440 / 20 = 35322 ∧
    706440 / 29 = 24360 ∧
    24360 / 20 = 1218 ∧
    35322 = 29 * 1218 := by decide

theorem ray_quotient_sizes5 :
    25 * 24 = 600 ∧
    600 / 24 = 25 ∧
    600 / 5 = 120 ∧
    120 / 24 = 5 ∧
    25 = 5 * 5 := by decide

/-- An order-p local character can remain nontrivial after quotient by
the prime-to-p cyclotomic torsion subgroup: its index is p. -/
theorem nontrivial_ray_quotient_image29 :
    35322 / 1218 = 29 := by decide

theorem nontrivial_ray_quotient_image5 :
    25 / 5 = 5 := by decide


/-!
## RHD-17B: an actual quotient map for root-invariant characters

The orbit of right multiplication by a specified root determines a
relation on any carrier G. We quotient by observational equality under
*all* Nat-valued functions invariant under that root step. The relation
is an equivalence, and any invariant modular character factors through
its quotient. In particular, a nonzero character witness survives.

This is a genuine Lean Quotient construction. The carrier is still an
abstract G; identifying it with R_wˣ and this relation with the cosets
of the concrete μ_n subgroup remains a separate original-source task.
-/

/-- Root-invariant observables cannot distinguish related elements. -/
def rootInvariantRel {G : Type} (f : G → G → G) (root : G)
    (x y : G) : Prop :=
  ∀ ψ : G → Nat, (∀ z, ψ (f z root) = ψ z) → ψ x = ψ y

/-- Equivalence induced by all root-invariant Nat-valued observables. -/
def rootInvariantSetoid {G : Type} (f : G → G → G) (root : G) :
    Setoid G where
  r := rootInvariantRel f root
  iseqv := ⟨
    (fun x ψ hψ => rfl),
    (fun x y hxy ψ hψ => (hxy ψ hψ).symm),
    (fun x y z hxy hyz ψ hψ => (hxy ψ hψ).trans (hyz ψ hψ))⟩

def rootInvariantQuotient {G : Type} (f : G → G → G) (root : G) :
    Type := Quotient (rootInvariantSetoid f root)

def rootInvariantClass {G : Type} (f : G → G → G) (root : G)
    (x : G) : rootInvariantQuotient f root :=
  Quotient.mk (rootInvariantSetoid f root) x

/-- One right-root step represents the same quotient class. -/
theorem rootInvariantClass_step {G : Type} (f : G → G → G)
    (root x : G) :
    rootInvariantClass f root x =
      rootInvariantClass f root (f x root) := by
  apply Quotient.sound
  intro ψ hψ
  exact (hψ x).symm

/-- Any modular character invariant under the root step factors
through the root-invariant quotient. -/
def descendedRootCharacter {G : Type} (f : G → G → G)
    (root : G) (char : G → Nat) (p : Nat)
    (h : ∀ x, char (f x root) % p = char x % p) :
    rootInvariantQuotient f root → Nat :=
  Quotient.lift (fun x => char x % p) (by
    intro x y hxy
    exact hxy (fun z => char z % p) h)

theorem descendedRootCharacter_class {G : Type}
    (f : G → G → G) (root : G) (char : G → Nat) (p : Nat)
    (h : ∀ x, char (f x root) % p = char x % p) (x : G) :
    descendedRootCharacter f root char p h
      (rootInvariantClass f root x) = char x % p := rfl

/-- Distinct character residues yield distinct quotient classes:
descent preserves every available nontriviality witness. -/
theorem rootInvariantClass_ne_of_char_ne {G : Type}
    (f : G → G → G) (root : G) (char : G → Nat) (p : Nat)
    (h : ∀ x, char (f x root) % p = char x % p)
    (x y : G) (hne : char x % p ≠ char y % p) :
    rootInvariantClass f root x ≠ rootInvariantClass f root y := by
  intro hxy
  apply hne
  calc
    char x % p =
        descendedRootCharacter f root char p h (rootInvariantClass f root x) := rfl
    _ = descendedRootCharacter f root char p h (rootInvariantClass f root y) :=
      congrArg (descendedRootCharacter f root char p h) hxy
    _ = char y % p := rfl

#print axioms primitive20_factor0
#print axioms primitive20_factor1
#print axioms primitive20_factor2
#print axioms primitive20_factor3
#print axioms primitive24_factor0
#print axioms primitive24_factor1
#print axioms primitive24_factor2
#print axioms primitive24_factor3
#print axioms character_constant_on_root_orbits
#print axioms ray_quotient_sizes29
#print axioms ray_quotient_sizes5
#print axioms nontrivial_ray_quotient_image29
#print axioms nontrivial_ray_quotient_image5
#print axioms rootInvariantClass_step
#print axioms descendedRootCharacter_class
#print axioms rootInvariantClass_ne_of_char_ne

end MathCan.RHLocalRayUnits

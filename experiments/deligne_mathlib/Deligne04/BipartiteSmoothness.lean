import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# DEL-08: characteristic-free algebraic Jacobian certificates

For a bipartite quadratic Q(x,y), Euler's identity in the x
variables says Q = sum_i x_i * (partial Q/partial x_i).
Consequently a hypersurface Q + c = 0 with c != 0 has a
nonzero partial derivative at every point on it.

This proves an exact algebraic smoothness certificate for the
unconstrained affine-space model, including the path quadratic
whose edges connect the even and odd vertices. It does not prove
that a generic section of an arbitrary smooth affine subvariety
U^k has the required weak Lefschetz property.
-/

open scoped BigOperators
open Finset

namespace Deligne08

/-- A bilinear quadratic on affine coordinates divided into two
sets, including all path-graph quadratic expressions. -/
def bipartiteQuadratic {K : Type*} [CommRing K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) K)
    (x : Fin n → K) (y : Fin m → K) : K :=
  ∑ i : Fin n, x i * (∑ j : Fin m, A i j * y j)

/-- Partial derivative with respect to an x coordinate. -/
def bipartitePartialX {K : Type*} [CommRing K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) K) (y : Fin m → K)
    (i : Fin n) : K :=
  ∑ j : Fin m, A i j * y j

/-- Euler identity in one group of bipartite variables. It
has no characteristic restriction and no factor of two. -/
theorem bipartite_euler_identity
    {K : Type*} [CommRing K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) K)
    (x : Fin n → K) (y : Fin m → K) :
    bipartiteQuadratic A x y =
      ∑ i : Fin n, x i * bipartitePartialX A y i := by
  rfl

/-- The equation Q+c=0 with c != 0 forces a nonvanishing
partial derivative with respect to at least one x coordinate,
over any field and indeed over any commutative ring. For n=0,
the level set is therefore empty. -/
theorem bipartite_nonzero_level_regular
    {K : Type*} [CommRing K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) K)
    (x : Fin n → K) (y : Fin m → K) (c : K)
    (hc : c ≠ 0)
    (hlevel : bipartiteQuadratic A x y + c = 0) :
    ∃ i : Fin n, bipartitePartialX A y i ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hQ : bipartiteQuadratic A x y = 0 := by
    rw [bipartite_euler_identity A x y]
    simp [h]
  have hc0 : c = 0 := by simpa [hQ] using hlevel
  exact hc hc0

/-- The affine conic xy + ax + by + c = 0 has a simultaneous
vanishing of both partial derivatives precisely when c = ab.
It is a characteristic-independent version of DEL-01's
hyperbola smoothness gate. -/
theorem hyperbola_singular_iff
    {K : Type*} [Field K] (a b c : K) :
    (∃ x y : K, x * y + a * x + b * y + c = 0 ∧
       x + b = 0 ∧ y + a = 0) ↔ c = a * b := by
  constructor
  · rintro ⟨x, y, hp, hx, hy⟩
    have hx' : x = -b := by linear_combination hx
    have hy' : y = -a := by linear_combination hy
    rw [hx', hy'] at hp
    calc
      c = a * b + ((-b) * (-a) + a * (-b) + b * (-a) + c) := by ring
      _ = a * b := by rw [hp]; ring
  · intro hc
    refine ⟨-b, -a, ?_, ?_, ?_⟩
    · rw [hc]
      ring
    · ring
    · ring

/-- If c is off the discriminant c=ab, at least one partial
derivative is nonzero at each point on the conic. -/
theorem hyperbola_regular_off_discriminant
    {K : Type*} [Field K] (a b c x y : K)
    (hc : c ≠ a * b)
    (hp : x * y + a * x + b * y + c = 0) :
    x + b ≠ 0 ∨ y + a ≠ 0 := by
  by_contra h
  push_neg at h
  apply hc
  exact (hyperbola_singular_iff a b c).mp
    ⟨x, y, hp, h.1, h.2⟩

#print axioms bipartite_euler_identity
#print axioms bipartite_nonzero_level_regular
#print axioms hyperbola_singular_iff
#print axioms hyperbola_regular_off_discriminant

end Deligne08

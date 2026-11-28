import MathCan.ObservableQuotient

/-!
NRF-04: finite families of observable-fiber-compatible update maps.

Lean checks structural closure of fiber compatibility under composition
and the existence of an induced map for each member of a compatible
finite family. It does not formalize rational rowspace rank,
Jacobian calculus, or the Jordan loss/leakage frontier.
-/

universe u v

namespace MathCan.ObservableFamily

open MathCan.ObservableQuotient

theorem compatible_compose
    {X : Type u} {Y : Type v} (obs : X → Y) (f g : X → X)
    (hf : FiberCompatible obs f)
    (hg : FiberCompatible obs g) :
    FiberCompatible obs (g ∘ f) := by
  intro a b hab
  exact hg (f a) (f b) (hf a b hab)

theorem finite_family_factor
    {X : Type u} {Y : Type v}
    (obs : X → Y) (maps : List (X → X))
    (surj : Function.Surjective obs)
    (hc : ∀ f ∈ maps, FiberCompatible obs f) :
    ∀ f ∈ maps, ∃ g : Y → Y, ∀ x : X, g (obs x) = obs (f x) := by
  intro f hf
  exact (factor_iff_fiber obs f surj).2 (hc f hf)

#print axioms compatible_compose
#print axioms finite_family_factor

end MathCan.ObservableFamily

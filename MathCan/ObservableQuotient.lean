import Init

/-!
# NRF-03: exact observable-fiber factorization

A surjective observation admits an induced deterministic map precisely when
the full-state map respects its observation fibers. This is a structural
theorem over arbitrary types; the quantitative norm/defect estimates in
the paired research note are paper-level.
-/

universe u v

namespace MathCan.ObservableQuotient

def FiberCompatible {X : Type u} {Y : Type v}
    (obs : X → Y) (f : X → X) : Prop :=
  ∀ a b, obs a = obs b → obs (f a) = obs (f b)

theorem factor_iff_fiber
    {X : Type u} {Y : Type v}
    (obs : X → Y) (f : X → X)
    (surj : Function.Surjective obs) :
    (∃ g : Y → Y, ∀ x : X, g (obs x) = obs (f x)) ↔
      FiberCompatible obs f := by
  constructor
  · rintro ⟨g, hg⟩ a b hab
    calc
      obs (f a) = g (obs a) := (hg a).symm
      _ = g (obs b) := congrArg g hab
      _ = obs (f b) := hg b
  · intro h
    classical
    let sec : Y → X := fun y => Classical.choose (surj y)
    have hs (y : Y) : obs (sec y) = y :=
      Classical.choose_spec (surj y)
    refine ⟨fun y => obs (f (sec y)), ?_⟩
    intro x
    exact h (sec (obs x)) x (hs (obs x))

theorem factor_unique
    {X : Type u} {Y : Type v}
    (obs : X → Y) (f : X → X)
    (surj : Function.Surjective obs)
    (g₁ g₂ : Y → Y)
    (h₁ : ∀ x, g₁ (obs x) = obs (f x))
    (h₂ : ∀ x, g₂ (obs x) = obs (f x)) :
    g₁ = g₂ := by
  funext y
  obtain ⟨x, hx⟩ := surj y
  rw [← hx, h₁ x, h₂ x]

#print axioms factor_iff_fiber
#print axioms factor_unique

end MathCan.ObservableQuotient

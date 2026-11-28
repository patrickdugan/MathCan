import Init

/-!
# NRF-05: combinatorial core of full-support gate saturation

The matrix determinant, exact binary32 reduction, and differentiable
tanh no-go theorem are proved in the companion paper and verified by
separate finite-field code. These Lean declarations formalize only the
support-propagation step.
-/

universe u

namespace MathCan.GateFamilyNoGo

def OneStep {ι : Type u} (seed : ι → Prop)
    (support : ι → ι → Prop) (target : ι) : Prop :=
  seed target ∨ ∃ source, seed source ∧ support source target

theorem full_support_saturates {ι : Type u}
    (seed : ι → Prop) (support : ι → ι → Prop)
    (nonempty : ∃ source, seed source)
    (dense : ∀ source target, support source target) :
    ∀ target, OneStep seed support target := by
  intro target
  obtain ⟨source, hs⟩ := nonempty
  exact Or.inr ⟨source, hs, dense source target⟩

theorem dense_closed_family_full {ι : Type u}
    (contained : ι → Prop) (support : ι → ι → Prop)
    (nonempty : ∃ source, contained source)
    (dense : ∀ source target, support source target)
    (closed : ∀ source target, contained source →
        support source target → contained target) :
    ∀ target, contained target := by
  intro target
  obtain ⟨source, hs⟩ := nonempty
  exact closed source target hs (dense source target)

#print axioms full_support_saturates
#print axioms dense_closed_family_full

end MathCan.GateFamilyNoGo

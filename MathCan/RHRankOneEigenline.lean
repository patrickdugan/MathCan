import Mathlib

/-!
# RHD-10: algebraic rank-one character eigenline

This is a genuine Lean theorem for an abstract group and a complex unit-valued
character. It is NOT an import of the RH source's `UA`, `RU`,
`IsAutRepU`, `SatU`, `SphOffU`, or `TyEll` definitions.
An adelic realization and local representation theory are separate gates.
-/

noncomputable section

namespace MathCan.RHRankOneEigenline

universe u
variable {G : Type u} [Group G]

/-- Abstract analogue of the rank-one automorphic function `φ(g)=ω(g)`. -/
def characterFunction (χ : G →* ℂˣ) : G → ℂ :=
  fun g => (χ g : ℂ)

/-- Right translation on functions on an abstract group. -/
def rightTranslate (h : G) (f : G → ℂ) : G → ℂ :=
  fun g => f (g * h)

/-- The genuine one-dimensional submodule spanned by the character function. -/
def eigenline (χ : G →* ℂˣ) : Submodule ℂ (G → ℂ) where
  carrier := {f | ∃ c : ℂ, f = c • characterFunction χ}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨a, rfl⟩
    rcases hg with ⟨b, rfl⟩
    refine ⟨a + b, ?_⟩
    simp [add_smul]
  smul_mem' := by
    intro a f hf
    rcases hf with ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    simp [mul_smul]

theorem character_mem_eigenline (χ : G →* ℂˣ) :
    characterFunction χ ∈ eigenline χ := by
  change ∃ c : ℂ, characterFunction χ = c • characterFunction χ
  exact ⟨1, by simp⟩

theorem character_nonzero (χ : G →* ℂˣ) :
    characterFunction χ ≠ 0 := by
  intro h
  have hOne : (1 : ℂ) = 0 := by
    simpa [characterFunction] using
      congrArg (fun f : G → ℂ => f 1) h
  exact one_ne_zero hOne

theorem character_right_eigen (χ : G →* ℂˣ) (h : G) :
    rightTranslate h (characterFunction χ) =
      (χ h : ℂ) • characterFunction χ := by
  funext g
  simp [rightTranslate, characterFunction, map_mul, smul_eq_mul, mul_comm]

theorem eigenline_right_eigen (χ : G →* ℂˣ) (h : G)
    (f : G → ℂ) (hf : f ∈ eigenline χ) :
    rightTranslate h f = (χ h : ℂ) • f := by
  rcases hf with ⟨c, rfl⟩
  funext g
  simp [rightTranslate, characterFunction, map_mul, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc]

theorem eigenline_right_invariant (χ : G →* ℂˣ) (h : G)
    (f : G → ℂ) (hf : f ∈ eigenline χ) :
    rightTranslate h f ∈ eigenline χ := by
  rw [eigenline_right_eigen χ h f hf]
  exact (eigenline χ).smul_mem (χ h : ℂ) hf

/-- The abstract eigenline contains a nonzero simultaneous right eigenvector. -/
theorem nonzero_right_eigenvector (χ : G →* ℂˣ) :
    ∃ f ∈ eigenline χ, f ≠ 0 ∧
      ∀ h : G, rightTranslate h f = (χ h : ℂ) • f := by
  exact ⟨characterFunction χ, character_mem_eigenline χ,
    character_nonzero χ, character_right_eigen χ⟩

/-- Finite index model of the other three primes of ℚ(ζ₂₀) above 29. -/
def otherRamified (w₀ : Fin 4) : Finset (Fin 4) :=
  Finset.univ.erase w₀

theorem selected_place_excluded (w₀ : Fin 4) :
    w₀ ∉ otherRamified w₀ := by
  simp [otherRamified]

theorem other_place_included (w₀ w : Fin 4) (h : w ≠ w₀) :
    w ∈ otherRamified w₀ := by
  simp [otherRamified, h]

theorem three_exceptional_places (w₀ : Fin 4) :
    (otherRamified w₀).card = 3 := by
  simp [otherRamified]

#print axioms character_mem_eigenline
#print axioms character_nonzero
#print axioms character_right_eigen
#print axioms eigenline_right_eigen
#print axioms eigenline_right_invariant
#print axioms nonzero_right_eigenvector
#print axioms three_exceptional_places

end MathCan.RHRankOneEigenline

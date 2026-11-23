import Deligne04.UniversalRelativeCritical
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic

/-!
# DEL-22C: exact ideal specialization for the universal relative critical incidence

DEL-22B proves that every universal original equation and augmented minor
specializes into the corresponding fixed-parameter ideal. The generators
actually specialize bijectively as indexed families. Applying `Ideal.map_span`
and `Ideal.map_sup` proves equality of their *extended ideals*, without
radicalization or assumptions about smoothness or Jacobian rank.

These statements concern a base change of ideals along the coefficient
evaluation homomorphism. They do not assert equality of inverse images
(comaps), which generally contain the coefficient-evaluation kernel.
-/

namespace Deligne22B

/-- The original DEL-16 scheme ideal specializes *exactly*, retaining
redundant equations and nilpotents (no radical is taken). -/
theorem universalOriginalIdeal_map_specialize
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (a : Deligne16.Coord k s → K) (c : K) :
    (universalOriginalIdeal f).map
        (MvPolynomial.map (parameterEval a c)) =
      Deligne16.productIdeal f := by
  classical
  unfold universalOriginalIdeal Deligne16.productIdeal
  rw [Ideal.map_span]
  congr 1
  ext q
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, (map_C_specialize a c (Deligne16.copyEquation f t)).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨t, rfl⟩, map_C_specialize a c (Deligne16.copyEquation f t)⟩

/-- The universal size-(d+1) augmented determinantal ideal specializes
to the complete DEL-22A minor ideal with equality. This includes all
repeated-index minors and uses the unmodified original Jacobian rows. -/
theorem universalMinorIdeal_map_specialize
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K) (d : ℕ) :
    (universalMinorIdeal f B d).map
        (MvPolynomial.map (parameterEval a c)) =
      Deligne22A.augmentedMinorIdeal f B a c d := by
  classical
  unfold universalMinorIdeal Deligne22A.augmentedMinorIdeal
  rw [Ideal.map_span]
  congr 1
  ext q
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨⟨rr, cc⟩, rfl⟩, rfl⟩
    exact ⟨(rr, cc),
      (universalMinor_specialize f B a c d rr cc).symm⟩
  · rintro ⟨⟨rr, cc⟩, rfl⟩
    exact ⟨_, ⟨(rr, cc), rfl⟩,
      universalMinor_specialize f B a c d rr cc⟩

/-- Specialization preserves the universal section's principal ideal
as an *ideal equality*, not merely generator membership. -/
theorem universalSectionIdeal_map_specialize
    {K : Type*} [Field K] {k s : ℕ}
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K) :
    (Ideal.span ({universalSection B} : Set
      (MvPolynomial (Deligne16.Coord k s)
        (ParameterRing K (Deligne16.Coord k s)))).map
        (MvPolynomial.map (parameterEval a c)) =
      Ideal.span ({Deligne16.fixedSection B a c} : Set
        (MvPolynomial (Deligne16.Coord k s) K))) := by
  classical
  rw [Ideal.map_span, Set.image_singleton]
  rw [universalSection_specialize]
  rfl

/-- Exact base-change equality of the *entire* original-scheme
relative-critical incidence ideal at fixed K-valued parameters. -/
theorem universalCriticalIdeal_map_specialize
    {K : Type*} [Field K] {k s r : ℕ}
    (f : Fin r → MvPolynomial (Fin s) K)
    (B : MvPolynomial (Deligne16.Coord k s) K)
    (a : Deligne16.Coord k s → K) (c : K) (d : ℕ) :
    (universalCriticalIdeal f B d).map
        (MvPolynomial.map (parameterEval a c)) =
      Deligne22A.fixedParameterCriticalIdeal f B a c d := by
  classical
  unfold universalCriticalIdeal Deligne22A.fixedParameterCriticalIdeal
  rw [Ideal.map_sup, Ideal.map_sup]
  rw [universalOriginalIdeal_map_specialize f a c]
  rw [universalSectionIdeal_map_specialize B a c]
  rw [universalMinorIdeal_map_specialize f B a c d]

#print axioms universalOriginalIdeal_map_specialize
#print axioms universalMinorIdeal_map_specialize
#print axioms universalSectionIdeal_map_specialize
#print axioms universalCriticalIdeal_map_specialize

end Deligne22B

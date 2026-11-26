module

public import TRR08Geometry.AffinePolynomial
public import TRR08Geometry.TameDecoder

/-!
# Transport of actual coordinate decoders

An additive equivalence of curve points with affine coordinate formulas
transports the cyclic subgroup and the assigned value at the identity.
The polynomial pullbacks preserve ordinary degree in each coordinate pair.
-/

@[expose] public section

namespace TRR08Geometry

open WeierstrassCurve

variable {K : Type} [Field K] [DecidableEq K] {W₁ W₂ : Affine K}

theorem assignedX_map_affine (e : W₁.Point ≃+ W₂.Point) (r : K)
    (hx : ∀ P : W₁.Point, P ≠ 0 → affineX (e P) = affineX P + r)
    (u : K) (P : W₁.Point) :
    assignedX (u+r) (e P) = assignedX u P + r := by
  classical
  by_cases hP : P = 0
  · subst P
    simp [assignedX]
  · have heP : e P ≠ 0 := fun h => hP (e.map_eq_zero_iff.mp h)
    simp [assignedX, hP, heP, hx P hP]

theorem affineX_symm_of_addEquiv (e : W₁.Point ≃+ W₂.Point) (r : K)
    (hx : ∀ P : W₁.Point, P ≠ 0 → affineX (e P) = affineX P + r)
    (P : W₂.Point) (hP : P ≠ 0) :
    affineX (e.symm P) = affineX P + (-r) := by
  have hne : e.symm P ≠ 0 := fun h => hP (e.symm.map_eq_zero_iff.mp h)
  have h := hx (e.symm P) hne
  rw [e.apply_symm_apply] at h
  simpa only [sub_eq_add_neg] using (eq_sub_iff_add_eq.mpr h.symm)

theorem affineY_symm_of_addEquiv (e : W₁.Point ≃+ W₂.Point) (r s t : K)
    (hx : ∀ P : W₁.Point, P ≠ 0 → affineX (e P) = affineX P + r)
    (hy : ∀ P : W₁.Point, P ≠ 0 →
      affineY (e P) = affineY P + s * affineX P + t)
    (P : W₂.Point) (hP : P ≠ 0) :
    affineY (e.symm P) = affineY P + (-s) * affineX P + (s*r-t) := by
  have hne : e.symm P ≠ 0 := fun h => hP (e.symm.map_eq_zero_iff.mp h)
  have h := hy (e.symm P) hne
  rw [e.apply_symm_apply, affineX_symm_of_addEquiv e r hx P hP] at h
  linear_combination -h

noncomputable def cyclicPointTransport (e : W₁.Point ≃+ W₂.Point) (T : W₁.Point)
    (P : AddSubgroup.zmultiples T) : AddSubgroup.zmultiples (e T) :=
  ⟨e (P : W₁.Point), by
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp P.property
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨n, ?_⟩
    rw [← map_zsmul, hn]⟩

theorem cyclicPointTransport_ne_zero (e : W₁.Point ≃+ W₂.Point) (T : W₁.Point)
    (P : AddSubgroup.zmultiples T) (hP : P ≠ 0) :
    cyclicPointTransport e T P ≠ 0 := by
  intro hz
  apply hP
  apply Subtype.ext
  apply e.map_eq_zero_iff.mp
  exact congrArg Subtype.val hz

noncomputable def decoderAffinePullback (r s t : K) (D : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  affineBlockOutput 1 (-r) (affineBlockPullback 1 r 1 s t D)

omit [DecidableEq K] in
theorem decoderAffinePullback_degree (r s t : K) {d : ℕ}
    (D : MvPolynomial (Fin 4) K) (hD : BlockDegreeLE d D) :
    BlockDegreeLE d (decoderAffinePullback r s t D) := by
  exact affineBlockOutput_degree 1 (-r) _ (affineBlockPullback_degree 1 r 1 s t D hD)

/-- Pulling back the inputs and the assigned output gives the original decoder. -/
theorem polynomialDecoder_affine_pullback (e : W₁.Point ≃+ W₂.Point) (r s t : K)
    (hx : ∀ P : W₁.Point, P ≠ 0 → affineX (e P) = affineX P + r)
    (hy : ∀ P : W₁.Point, P ≠ 0 →
      affineY (e P) = affineY P + s * affineX P + t)
    (T : W₁.Point) (u : K) (D : MvPolynomial (Fin 4) K)
    (hD : PolynomialDecoderOn (AddSubgroup.zmultiples (e T)) (u+r) D) :
    PolynomialDecoderOn (AddSubgroup.zmultiples T) u (decoderAffinePullback r s t D) := by
  intro P Q hP hQ
  have hP₀ : (P : W₁.Point) ≠ 0 := fun h => hP (Subtype.ext h)
  have hQ₀ : (Q : W₁.Point) ≠ 0 := fun h => hQ (Subtype.ext h)
  have hd := hD (cyclicPointTransport e T P) (cyclicPointTransport e T Q)
    (cyclicPointTransport_ne_zero e T P hP) (cyclicPointTransport_ne_zero e T Q hQ)
  change blockEval D (affineX (e (P : W₁.Point))) (affineY (e (P : W₁.Point)))
      (affineX (e (Q : W₁.Point))) (affineY (e (Q : W₁.Point))) =
      assignedX (u+r) (e (P : W₁.Point) + e (Q : W₁.Point)) at hd
  simp only [decoderAffinePullback, affineBlockOutput_eval, affineBlockPullback_eval, one_mul]
  rw [← hx (P : W₁.Point) hP₀, ← hy (P : W₁.Point) hP₀,
    ← hx (Q : W₁.Point) hQ₀, ← hy (Q : W₁.Point) hQ₀]
  rw [hd, ← map_add e, assignedX_map_affine e r hx u]
  change assignedX u ((P : W₁.Point) + (Q : W₁.Point)) + r + (-r) =
    assignedX u ((P : W₁.Point) + (Q : W₁.Point))
  ring

/-- The same ordinary block bound is attainable in either affine coordinate model. -/
theorem cyclic_polynomialDecoder_affine_iff (e : W₁.Point ≃+ W₂.Point) (r s t : K)
    (hx : ∀ P : W₁.Point, P ≠ 0 → affineX (e P) = affineX P + r)
    (hy : ∀ P : W₁.Point, P ≠ 0 →
      affineY (e P) = affineY P + s * affineX P + t)
    (T : W₁.Point) (d : ℕ) (u : K) :
    (∃ D : MvPolynomial (Fin 4) K,
      BlockDegreeLE d D ∧ PolynomialDecoderOn (AddSubgroup.zmultiples T) u D) ↔
    (∃ D : MvPolynomial (Fin 4) K,
      BlockDegreeLE d D ∧ PolynomialDecoderOn (AddSubgroup.zmultiples (e T)) (u+r) D) := by
  constructor
  · rintro ⟨D, hdegree, hdecoder⟩
    refine ⟨decoderAffinePullback (-r) (-s) (s*r-t) D,
      decoderAffinePullback_degree (-r) (-s) (s*r-t) D hdegree, ?_⟩
    apply polynomialDecoder_affine_pullback e.symm (-r) (-s) (s*r-t)
      (affineX_symm_of_addEquiv e r hx) (affineY_symm_of_addEquiv e r s t hx hy)
      (e T) (u+r) D
    simpa using hdecoder
  · rintro ⟨D, hdegree, hdecoder⟩
    exact ⟨decoderAffinePullback r s t D, decoderAffinePullback_degree r s t D hdegree,
      polynomialDecoder_affine_pullback e r s t hx hy T u D hdecoder⟩

end TRR08Geometry

#print axioms TRR08Geometry.assignedX_map_affine
#print axioms TRR08Geometry.affineX_symm_of_addEquiv
#print axioms TRR08Geometry.affineY_symm_of_addEquiv
#print axioms TRR08Geometry.cyclicPointTransport_ne_zero
#print axioms TRR08Geometry.decoderAffinePullback_degree
#print axioms TRR08Geometry.polynomialDecoder_affine_pullback
#print axioms TRR08Geometry.cyclic_polynomialDecoder_affine_iff

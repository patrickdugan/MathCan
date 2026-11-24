/-
Adapter for the pinned Anthropic VP/VNP development at
11b6c7e3c927df2658f513b6b68ea7f8929c62c5.
The radius/localization proof follows Paper/Gauges.lean
(Copyright (c) 2026 Anthropic, PBC; Apache-2.0).
The countable compactness route is MathCan research.
-/
import Paper.Gauges
import FiveTrackMinimum

open scoped BigOperators
open Ov Ov.Ten Ov.Duality

namespace VPVNP.Upstream

section Canonical

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- Finite index sets are canonicalized to Fin d. Raw Ten is not asserted
    to be countable, because it ranges over arbitrary index types. -/
abbrev Canonical (K I : Type) :=
  Σ d : I → ℕ, ((i : I) → Fin (d i)) → K

def canonicalTensor (a : Canonical K I) : Ten K I where
  ι i := Fin (a.1 i)
  fin := fun _ => inferInstance
  dec := fun _ => inferInstance
  val := a.2

theorem canonical_surjective :
    Function.Surjective (fun a : Canonical K I => cls (canonicalTensor a)) := by
  intro m
  let t := rep m
  let e : ∀ i, t.ι i ≃ Fin (Fintype.card (t.ι i)) :=
    fun i => Fintype.equivFin (t.ι i)
  let a : Canonical K I :=
    ⟨fun i => Fintype.card (t.ι i), fun x => t.val (fun i => (e i).symm (x i))⟩
  refine ⟨a, ?_⟩
  rw [← cls_rep m]
  change cls (canonicalTensor a) = cls t
  apply cls_eq.2
  exact Ten.Equi.of_equiv (fun i => (e i).symm) (fun _ => rfl)

theorem countable_tensor_classes [Countable K] : Countable (Cls K I) :=
  (canonical_surjective (K := K) (I := I)).countable

/-- The finite-cover restriction of the actual upstream tensor monoid. -/
noncomputable def indexedCover : VPVNP.Five.Covers (Cls K I) :=
  fun _ t b => (tenCover K I).cov t b

theorem gauge_to_indexed {p : Cls K I → ℝ} (h : IsPre (tenCover K I) p) :
    VPVNP.Five.IsGauge (indexedCover (K := K) (I := I)) p :=
  ⟨h.nonneg, h.one, h.mul_le, fun _ t b hb => h.le_sum t b hb⟩

theorem indexed_to_gauge {p : Cls K I → ℝ}
    (h : VPVNP.Five.IsGauge (indexedCover (K := K) (I := I)) p) :
    IsPre (tenCover K I) p := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro κ _ t b hb
  let e := (Fintype.equivFin κ).symm
  have hcov : (indexedCover (K := K) (I := I)) (Fintype.card κ) t
      (fun j => b (e j)) := by
    change Ten.SumRestr (rep t) (fun j => rep (b (e j)))
    exact hb.reindex e
  exact (h.2.2.2 _ t _ hcov).trans_eq (Fintype.sum_equiv e _ _ fun _ => rfl)

theorem upstream_minimal_countable {p₀ : Cls K I → ℝ}
    (h₀ : IsPre (tenCover K I) p₀) (e : ℕ → Cls K I)
    (he : Function.Surjective e) :
    ∃ p : Cls K I → ℝ, IsPre (tenCover K I) p ∧
      (∀ t, p t ≤ p₀ t) ∧
      (∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps p x y c) ∧
      ∀ q : Cls K I → ℝ, IsPre (tenCover K I) q →
        (∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps q x y c) →
        (∀ t, q t ≤ p t) → ∀ t, q t = p t := by
  obtain ⟨p, hp, hle, hk, hmin⟩ :=
    VPVNP.Five.gauge_minimal_countable (indexedCover (K := K) (I := I))
      p₀ (gauge_to_indexed h₀) e he
  exact ⟨p, indexed_to_gauge hp, hle, hk,
    fun q hq hqk hqp => hmin q (gauge_to_indexed hq) hqk hqp⟩

open Ov.Duality.IsPre

/-- Reuse the upstream radius/localization steps with the replacement
    minimality theorem. The published Zorn-based minimality theorem is
    absent from this proof's direct references. -/
theorem upstream_spectral_monoid_countable {p₀ : Cls K I → ℝ}
    (h₀ : IsPre (tenCover K I) p₀) (e : ℕ → Cls K I)
    (he : Function.Surjective e) :
    ∃ F : Cls K I → ℝ, IsPre (tenCover K I) F ∧
      (∀ s t, F (s*t) = F s * F t) ∧ (∀ t, F t ≤ p₀ t) ∧
      ∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps F x y c := by
  obtain ⟨p, hp, hle, hkeep, hmin⟩ := upstream_minimal_countable h₀ e he
  have hrad : ∀ t, sInf (rad p t) = p t :=
    hmin _ (Paper.prop_gauge_radius hp)
      (fun x y c hc hk => Paper.prop_gauge_radius_keeps hp hc (hkeep x y c hc hk))
      (Paper.prop_gauge_radius_le hp)
  refine ⟨p, hp, fun s f => le_antisymm (hp.mul_le s f) ?_, hle, hkeep⟩
  rcases (hp.nonneg f).eq_or_lt with hf | hf
  · rw [← hf, mul_zero]
    exact hp.nonneg _
  · obtain ⟨q, hq, hqle, hqk, hqkeep⟩ :=
      Paper.prop_gauge_localize hp hf (Paper.prop_gauge_radius_pow hp hrad f)
    have hqp := hmin q hq (fun x y c hc hk => hqkeep x y c hc (hkeep x y c hc hk)) hqle
    have h1 := hqk s
    rw [hqp, hqp, mul_one, inv_mul_eq_div, le_div_iff₀ hf] at h1
    exact h1

/-- Proposition A.5 for countable fields, with precisely the upstream
    spectral-point statement (all kept triples, arbitrary finite tensors). -/
theorem prop_gauge_countable [Countable K] (p : PreSpec K I) :
    ∃ φ : Spec K I, (∀ t, φ.F t ≤ p.p t) ∧
      ∀ (x y : Ten K I) (c : ℝ), 0 ≤ c → (∀ t, p.p (t*x) ≤ c * p.p (t*y)) →
        ∀ t, φ.F (t*x) ≤ c * φ.F (t*y) := by
  letI : Countable (Cls K I) := countable_tensor_classes
  letI : Nonempty (Cls K I) := ⟨1⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Cls K I)
  obtain ⟨F, hF, hmul, hle, hk⟩ :=
    upstream_spectral_monoid_countable (isPre_onCls p) e he
  refine ⟨⟨fun t => F (cls t), fun _ => hF.nonneg _, hF.one,
    fun s t => by rw [cls_mul, hmul],
    fun s b hb => hF.le_sum _ _ (tenCover_cov.2 hb)⟩, fun t => ?_, fun x y c hc h t => ?_⟩
  · exact (hle (cls t)).trans (onCls_cls p t).le
  · have h1 := hk (cls x) (cls y) c hc (keeps_onCls h) (cls t)
    rwa [← cls_mul, ← cls_mul] at h1

end Canonical
end VPVNP.Upstream

#print axioms VPVNP.Upstream.canonical_surjective
#print axioms VPVNP.Upstream.countable_tensor_classes
#print axioms VPVNP.Upstream.gauge_to_indexed
#print axioms VPVNP.Upstream.indexed_to_gauge
#print axioms VPVNP.Upstream.upstream_minimal_countable
#print axioms VPVNP.Upstream.upstream_spectral_monoid_countable
#print axioms VPVNP.Upstream.prop_gauge_countable

import Mathlib

/-!
VPVNP-FIVE-02: countably indexed gauge minimization and wire-cut obstruction.
The compactness lemma uses Mathlib's classical topology. Its axiom report is
not a claim that the entire upstream proof has been recast in choice-free Lean.
The geometric integration theorem exposes its projection-averaging inputs.
-/
open Set
open scoped BigOperators

namespace VPVNP.Five

section Minimum

variable {M : Type*}

/-- A minimum face retains all minimizers of one coordinate. -/
def minFace (S : Set (M → ℝ)) (i : M) : Set (M → ℝ) :=
  S ∩ ⋂ r : S, {q | q i ≤ r.val i}

theorem mem_minFace {S : Set (M → ℝ)} {i : M} {q : M → ℝ} :
    q ∈ minFace S i ↔ q ∈ S ∧ ∀ r ∈ S, q i ≤ r i := by
  constructor
  · intro h
    change q ∈ S ∧ q ∈ ⋂ r : S, {q | q i ≤ r.val i} at h
    refine ⟨h.1, fun r hr => ?_⟩
    exact Set.mem_iInter.mp h.2 ⟨r, hr⟩
  · rintro ⟨hq, h⟩
    change q ∈ S ∧ q ∈ ⋂ r : S, {q | q i ≤ r.val i}
    exact ⟨hq, Set.mem_iInter.mpr (fun r => h r.val r.property)⟩

theorem minFace_subset (S : Set (M → ℝ)) (i : M) :
    minFace S i ⊆ S := fun _ h => (mem_minFace.mp h).1

theorem minFace_closed {S : Set (M → ℝ)} (hS : IsClosed S) (i : M) :
    IsClosed (minFace S i) := by
  unfold minFace
  exact hS.inter (isClosed_iInter fun r =>
    isClosed_le (continuous_apply i) continuous_const)

theorem minFace_nonempty {S : Set (M → ℝ)} (hS : IsCompact S)
    (hn : S.Nonempty) (i : M) : (minFace S i).Nonempty := by
  obtain ⟨q, hq, hmin⟩ :=
    hS.exists_isMinOn hn (continuous_apply i).continuousOn
  exact ⟨q, mem_minFace.mpr ⟨hq, fun r hr => hmin hr⟩⟩

/-- The recursion is set-valued and does not pick a witness at each step. -/
def minFaces (S : Set (M → ℝ)) (e : ℕ → M) : ℕ → Set (M → ℝ)
  | 0 => S
  | n+1 => minFace (minFaces S e n) (e n)

theorem compact_coordinate_minimal (S : Set (M → ℝ)) (e : ℕ → M)
    (he : Function.Surjective e) (hS : IsCompact S) (hn : S.Nonempty) :
    ∃ p ∈ S, ∀ q ∈ S, (∀ i, q i ≤ p i) → q = p := by
  have hstep : ∀ n, minFaces S e (n+1) ⊆ minFaces S e n :=
    fun n => minFace_subset _ _
  have hanti : Antitone (minFaces S e) := antitone_nat_of_succ_le hstep
  have hclosed : ∀ n, IsClosed (minFaces S e n) := by
    intro n
    induction n with
    | zero => exact hS.isClosed
    | succ n ih => exact minFace_closed ih _
  have hc : ∀ n, IsCompact (minFaces S e n) := fun n =>
    hS.of_isClosed_subset (hclosed n) (hanti (Nat.zero_le n))
  have hnon : ∀ n, (minFaces S e n).Nonempty := by
    intro n
    induction n with
    | zero => exact hn
    | succ n ih => exact minFace_nonempty (hc n) ih _
  obtain ⟨p, hp⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (minFaces S e) hstep hnon hS hclosed
  have hp' : ∀ n, p ∈ minFaces S e n := Set.mem_iInter.mp hp
  refine ⟨p, hp' 0, ?_⟩
  intro q hq hle
  have hq' : ∀ n, q ∈ minFaces S e n := by
    intro n
    induction n with
    | zero => exact hq
    | succ n ih =>
      have hpmin : ∀ r ∈ minFaces S e n, p (e n) ≤ r (e n) :=
        (mem_minFace.mp (hp' (n+1))).2
      exact mem_minFace.mpr ⟨ih, fun r hr => (hle (e n)).trans (hpmin r hr)⟩
  funext i
  obtain ⟨n, rfl⟩ := he i
  exact le_antisymm (hle (e n))
    ((mem_minFace.mp (hp' (n+1))).2 q (hq' n))

end Minimum

section Gauge

variable {M : Type*} [CommMonoid M]

/-- Finite cover interface. The finite-list encoding is sufficient for the
    tensor-cover relation after reindexing a finite cover. -/
abbrev Covers (M : Type*) := ∀ n : ℕ, M → (Fin n → M) → Prop

def IsGauge (C : Covers M) (p : M → ℝ) : Prop :=
  (∀ t, 0 ≤ p t) ∧ p 1 = 1 ∧
  (∀ a b, p (a*b) ≤ p a * p b) ∧
  (∀ n a b, C n a b → p a ≤ ∑ j, p (b j))

def Keeps (p : M → ℝ) (x y : M) (c : ℝ) : Prop :=
  ∀ t, p (t*x) ≤ c * p (t*y)

def gaugeFeasible (C : Covers M) (p₀ : M → ℝ) : Set (M → ℝ) :=
  {p | ∀ t, p t ∈ Icc 0 (p₀ t)} ∩
  ({p | p 1 = 1} ∩
  ((⋂ a : M, ⋂ b : M, {p | p (a*b) ≤ p a * p b}) ∩
  ((⋂ n : ℕ, ⋂ a : M, ⋂ b : Fin n → M, ⋂ (_h : C n a b),
    {p | p a ≤ ∑ j, p (b j)}) ∩
  (⋂ x : M, ⋂ y : M, ⋂ c : ℝ, ⋂ (_hc : 0 ≤ c),
    ⋂ (_hk : Keeps p₀ x y c), ⋂ t : M,
    {p | p (t*x) ≤ c * p (t*y)}))))

theorem mem_gaugeFeasible {C : Covers M} {p₀ p : M → ℝ} :
    p ∈ gaugeFeasible C p₀ ↔
      IsGauge C p ∧ (∀ t, p t ≤ p₀ t) ∧
      ∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps p x y c := by
  simp only [gaugeFeasible, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_setOf_eq, Set.mem_Icc, IsGauge, Keeps]
  constructor
  · rintro ⟨hbox, hone, hmul, hcov, hkeep⟩
    exact ⟨⟨fun t => (hbox t).1, hone, hmul, hcov⟩,
      fun t => (hbox t).2, hkeep⟩
  · rintro ⟨⟨hn, hone, hmul, hcov⟩, hle, hkeep⟩
    exact ⟨fun t => ⟨hn t, hle t⟩, hone, hmul, hcov, hkeep⟩

theorem gaugeFeasible_compact (C : Covers M) (p₀ : M → ℝ) :
    IsCompact (gaugeFeasible C p₀) := by
  have hbox : IsCompact {p : M → ℝ | ∀ t, p t ∈ Icc 0 (p₀ t)} :=
    isCompact_pi_infinite fun t => isCompact_Icc
  have hclosed : IsClosed (gaugeFeasible C p₀) := by
    unfold gaugeFeasible
    apply hbox.isClosed.inter
    apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    apply IsClosed.inter
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      exact isClosed_le (by fun_prop) (by fun_prop)
    apply IsClosed.inter
    · refine isClosed_iInter fun n => isClosed_iInter fun a =>
        isClosed_iInter fun b => isClosed_iInter fun _ => ?_
      exact isClosed_le (by fun_prop) (by fun_prop)
    · refine isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_iInter fun c => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_iInter fun t => ?_
      exact isClosed_le (by fun_prop) (by fun_prop)
  exact hbox.of_isClosed_subset hclosed (fun _ h => h.1)

/-- Countable replacement for the Zorn minimality interface in Proposition A.5.
    It retains every nonnegative kept triple, not merely a selected list. -/
theorem gauge_minimal_countable (C : Covers M) (p₀ : M → ℝ)
    (h₀ : IsGauge C p₀) (e : ℕ → M) (he : Function.Surjective e) :
    ∃ p : M → ℝ, IsGauge C p ∧ (∀ t, p t ≤ p₀ t) ∧
      (∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps p x y c) ∧
      ∀ q : M → ℝ, IsGauge C q →
        (∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps q x y c) →
        (∀ t, q t ≤ p t) → ∀ t, q t = p t := by
  have hn : (gaugeFeasible C p₀).Nonempty :=
    ⟨p₀, mem_gaugeFeasible.mpr ⟨h₀, fun _ => le_rfl, fun _ _ _ _ h => h⟩⟩
  obtain ⟨p, hp, hmin⟩ :=
    compact_coordinate_minimal (gaugeFeasible C p₀) e he
      (gaugeFeasible_compact C p₀) hn
  obtain ⟨hg, hle, hk⟩ := mem_gaugeFeasible.mp hp
  refine ⟨p, hg, hle, hk, fun q hq hqk hqp t => ?_⟩
  have hqmem : q ∈ gaugeFeasible C p₀ :=
    mem_gaugeFeasible.mpr ⟨hq, fun i => (hqp i).trans (hle i), hqk⟩
  exact congrFun (hmin q hqmem hqp) t

end Gauge

section Geometry

open MeasureTheory

/-- Rank bound implies cut capacity plus logarithmic selector overhead. -/
theorem logarithmic_cut (r b : ℕ) (A : ℝ) (hA : 0 < A)
    (hr : (2:ℝ)^r ≤ A * (2:ℝ)^b) :
    (r:ℝ) ≤ (b:ℝ) + Real.log A / Real.log 2 := by
  have h := Real.log_le_log (by positivity : 0 < (2:ℝ)^r) hr
  rw [Real.log_pow, Real.log_mul hA.ne' (by positivity), Real.log_pow] at h
  have hp := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hd : (r:ℝ) - (b:ℝ) ≤ Real.log A / Real.log 2 :=
    (le_div_iff₀ hp).2 (by linarith)
  linarith

/-- One capacity envelope suffices, including a fixed common layout. -/
theorem sum_rank_cut {J : Type*} [Fintype J] [Nonempty J]
    (r B : ℕ) (b : J → ℕ)
    (hr : (2:ℝ)^r ≤ ∑ j : J, (2:ℝ)^(b j))
    (hB : ∀ j, b j ≤ B) :
    (r:ℝ) ≤ (B:ℝ) + Real.log (Fintype.card J : ℝ) / Real.log 2 := by
  have hs : (∑ j : J, (2:ℝ)^(b j)) ≤ (Fintype.card J : ℝ) * (2:ℝ)^B := by
    calc
      _ ≤ ∑ _ : J, (2:ℝ)^B := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (hB j)
      _ = _ := by simp
  exact logarithmic_cut r B _ (by exact_mod_cast Fintype.card_pos) (hr.trans hs)

/-- Thresholds separating two projected endpoints form a half-open interval
    of length equal to their projected separation. -/
theorem projected_edge_integral (a b w : ℝ) :
    (∫ t : ℝ, (Set.uIoc a b).indicator (fun _ : ℝ => w) t) =
      |b-a| * w := by
  rw [integral_indicator_const w measurableSet_uIoc]
  simp [Measure.real, Real.volume_uIoc, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

/-- Abstract cut-average interface: the measure has mass two (thresholds in
    [-1,1] and normalized directions).  The two integral equalities express
    directional averaging of projected wire lengths. -/
theorem integrated_cut_obstruction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (r b : X → ℝ)
    (c W target L : ℝ) (hc : 0 < c) (hvol : μ.real Set.univ = 2)
    (hr : Integrable r μ) (hb : Integrable b μ)
    (hcut : ∀ x, r x ≤ b x + L)
    (hR : (∫ x, r x ∂μ) = c * target)
    (hB : (∫ x, b x ∂μ) = c * W) :
    target ≤ W + (2/c)*L := by
  have hconst : Integrable (fun _ : X => L) μ := integrable_const L
  have hi := integral_mono hr (hb.add hconst) hcut
  change (∫ x, r x ∂μ) ≤ ∫ x, b x + L ∂μ at hi
  rw [integral_add hb hconst, hR, hB, integral_const, hvol, smul_eq_mul] at hi
  have hd : target - W ≤ (2*L)/c :=
    (le_div_iff₀ hc).2 (by nlinarith)
  have he : (2*L)/c = (2/c)*L := by ring
  linarith

/-- The first absolute moment dominates the second moment of a bounded
    coordinate. For a rotation-invariant sphere the latter is 1/D. -/
theorem coordinate_abs_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : X → ℝ)
    (hbounded : ∀ x, |u x| ≤ 1)
    (hs : Integrable (fun x => (u x)^2) μ)
    (ha : Integrable (fun x => |u x|) μ) :
    (∫ x, (u x)^2 ∂μ) ≤ ∫ x, |u x| ∂μ := by
  apply integral_mono hs ha
  intro x
  calc
    (u x)^2 = |u x|^2 := (sq_abs _).symm
    _ ≤ |u x| := by
      have hh := mul_nonneg (abs_nonneg (u x)) (sub_nonneg.mpr (hbounded x))
      nlinarith only [hh]

/-- Numerical endpoint of the common-layout obstruction. -/
theorem no_strict_shortening (D : ℕ) (c W target L : ℝ)
    (hc : 0 < c) (hcd : 1 ≤ c * (D:ℝ)) (hL : 0 ≤ L)
    (havg : target ≤ W + (2/c)*L) :
    target ≤ W + 2*(D:ℝ)*L := by
  have hcoef : 2/c ≤ 2*(D:ℝ) :=
    (div_le_iff₀ hc).2 (by nlinarith)
  have hh := mul_le_mul_of_nonneg_right hcoef hL
  linarith only [havg, hh]

end Geometry
end VPVNP.Five

#print axioms VPVNP.Five.mem_minFace
#print axioms VPVNP.Five.minFace_subset
#print axioms VPVNP.Five.minFace_closed
#print axioms VPVNP.Five.minFace_nonempty
#print axioms VPVNP.Five.compact_coordinate_minimal
#print axioms VPVNP.Five.mem_gaugeFeasible
#print axioms VPVNP.Five.gaugeFeasible_compact
#print axioms VPVNP.Five.gauge_minimal_countable
#print axioms VPVNP.Five.logarithmic_cut
#print axioms VPVNP.Five.sum_rank_cut
#print axioms VPVNP.Five.projected_edge_integral
#print axioms VPVNP.Five.integrated_cut_obstruction
#print axioms VPVNP.Five.coordinate_abs_moment
#print axioms VPVNP.Five.no_strict_shortening

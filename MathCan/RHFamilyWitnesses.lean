import Init

/-!
# RHD-02: family-witness quantifiers and cardinality floors

Pure logical and integer-arithmetic consequences of the hypothesis shape
in the Alpoge/Claude Dirichlet-GRH/RH Lean source.

Source:
leanprover-community/riemann-hypothesis
commit f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3
Formalism/SharpRestriction/GlobalSchurBounds/ZetaZeroFreeRegion.lean
Formalism/SharpRestriction/GlobalSchurBounds/RamificationTwoAndConjugationAtQAndD.lean

No construction of D7, Scale, Gc, theta, adm5, adm6, or adm7 is asserted.
Time is abstracted to Nat so MathCan can use Lean 4.35 + Init.
-/

namespace MathCan.RHFamilyWitnesses

universe u

/-- A property holds uniformly for every member of the dependent family
after a *single* eventual threshold. -/
def EventuallyAll {Ix : Nat → Type u}
    (P : (n : Nat) → Ix n → Prop) : Prop :=
  ∃ cutoff : Nat, ∀ n : Nat, cutoff ≤ n → ∀ i : Ix n, P n i

/-- There is a valid family index at each sufficiently large scale.
The index is allowed to vary with the scale. -/
def EventuallyExists {Ix : Nat → Type u}
    (P : (n : Nat) → Ix n → Prop) : Prop :=
  ∃ cutoff : Nat, ∀ n : Nat, cutoff ≤ n → ∃ i : Ix n, P n i

/-- Uniform adm5, adm6 and size bounds can be combined with an eventual
adm7-selected index. This is the quantified combinatorial step in
proposition_eleven_two_along_family, abstracting away the analytic details. -/
theorem synchronized_family_witnesses
    {Ix : Nat → Type u}
    (P5 P6 PSize PTop : (n : Nat) → Ix n → Prop)
    (h5 : EventuallyAll P5)
    (h6 : EventuallyAll P6)
    (hS : EventuallyAll PSize)
    (hT : EventuallyExists PTop) :
    EventuallyExists (fun n i => P5 n i ∧ P6 n i ∧
      PSize n i ∧ PTop n i) := by
  obtain ⟨b5, h5'⟩ := h5
  obtain ⟨b6, h6'⟩ := h6
  obtain ⟨bS, hS'⟩ := hS
  obtain ⟨bT, hT'⟩ := hT
  refine ⟨b5 + b6 + bS + bT, ?_⟩
  intro n hn
  have hn5 : b5 ≤ n := by omega
  have hn6 : b6 ≤ n := by omega
  have hnS : bS ≤ n := by omega
  have hnT : bT ≤ n := by omega
  obtain ⟨i, hTi⟩ := hT' n hnT
  exact ⟨i, h5' n hn5 i, h6' n hn6 i, hS' n hnS i, hTi⟩

/-- At each sufficiently large scale, an adm7-like witness makes the
family index type inhabited. This rules out a globally empty family
whenever eventual existence has been established. -/
theorem eventual_selected_index_forces_nonempty
    {Ix : Nat → Type u} (P : (n : Nat) → Ix n → Prop)
    (h : EventuallyExists P) :
    ∃ cutoff : Nat, ∀ n : Nat, cutoff ≤ n → Nonempty (Ix n) := by
  obtain ⟨cutoff, hcutoff⟩ := h
  refine ⟨cutoff, ?_⟩
  intro n hn
  obtain ⟨i, _⟩ := hcutoff n hn
  exact ⟨i⟩

/-- A universal bound alone is vacuous when its family has no indices. -/
theorem empty_index_family_satisfies_every_eventual_universal :
    EventuallyAll (Ix := fun _ => Empty) (fun _ _ => False) := by
  refine ⟨0, ?_⟩
  intro n hn i
  exact Empty.elim i

/-- The existential part of TOPF excludes that empty-index situation. -/
theorem empty_index_family_fails_eventual_existence :
    ¬ EventuallyExists (Ix := fun _ => Empty) (fun _ _ => True) := by
  intro h
  obtain ⟨cutoff, hcutoff⟩ := h
  obtain ⟨i, _⟩ := hcutoff cutoff (Nat.le_refl cutoff)
  exact Empty.elim i

/-- There can be an appropriate family index for every scale while
no single index remains appropriate at every scale. -/
def alternatingIndexValid (n index : Nat) : Prop := index = n % 2

theorem selected_index_may_depend_on_scale :
    ∀ n : Nat, ∃ i : Nat, alternatingIndexValid n i := by
  intro n
  exact ⟨n % 2, rfl⟩

theorem alternating_selection_has_no_fixed_index :
    ¬ ∃ i : Nat, ∀ n : Nat, alternatingIndexValid n i := by
  rintro ⟨i, h⟩
  have h0 : i = 0 := by simpa [alternatingIndexValid] using h 0
  have h1 : i = 1 := by simpa [alternatingIndexValid] using h 1
  omega

/-- Scale-wise constants cannot in general be replaced by one
uniform constant that works at all scales. This records a critical
quantifier-order distinction in the upstream AllLargeC predicate. -/
theorem scale_dependent_constants_are_weaker_than_uniform :
    (∀ n : Nat, ∃ C : Nat, n ≤ C) ∧
      ¬ (∃ C : Nat, ∀ n : Nat, n ≤ C) := by
  constructor
  · intro n
    exact ⟨n, Nat.le_refl n⟩
  · rintro ⟨C, h⟩
    have hc := h (C + 1)
    omega

/-- Source SizesAt n >= x^(2+31eps/4), combined with
PlacesAt TT >= n*x^(-eps/8)/2 and T2 >= n*x^(-eps),
forces very large selected subsets.

Write L=log₂x and q=eps*L, with all logarithms integral.
The premises are the denominator-cleared source inequalities.
The conclusions are lower bounds on 2-adic logarithms of
TT and T2 cardinalities, before any analytic witness is constructed. -/
theorem character_subsets_inherit_quadratic_scale
    (L q nLog nTLog nT2Log : Nat)
    (hRank : 8 * L + 31 * q ≤ 4 * nLog)
    (hTT : 8 * nLog ≤ 8 * nTLog + q + 8)
    (hT2 : nLog ≤ nT2Log + q) :
    16 * L + 61 * q ≤ 8 * nTLog + 8 ∧
    8 * L + 27 * q ≤ 4 * nT2Log := by
  omega

#print axioms synchronized_family_witnesses
#print axioms eventual_selected_index_forces_nonempty
#print axioms empty_index_family_satisfies_every_eventual_universal
#print axioms empty_index_family_fails_eventual_existence
#print axioms selected_index_may_depend_on_scale
#print axioms alternating_selection_has_no_fixed_index
#print axioms scale_dependent_constants_are_weaker_than_uniform
#print axioms character_subsets_inherit_quadratic_scale

end MathCan.RHFamilyWitnesses

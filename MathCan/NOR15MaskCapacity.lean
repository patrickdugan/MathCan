import Init

/-!
# NOR-15D: capacity of observable equivalence classes

If a policy can observe only a public-signature class, it must select the
same candidate for every source in that class. The number of future-correct
cases in the class is bounded by a certified candidate-wise maximum.
Because signatures define disjoint groups, the total bound is the sum of
those group-wise maxima.

The arithmetic instance 25/40 uses fourteen maxima read from the frozen
NOR-15C receipt. The Lean kernel verifies the algebra and 14-element sum,
not the empirical association between those maxima and external JSON.
-/

namespace MathCan.NOR15MaskCapacity

universe u v
variable {Group : Type u} {Candidate : Type v}

/-- Sum of exact future-success counts over public-signature groups. -/
def groupSuccessTotal
    (groups : List Group)
    (score : Group → Candidate → Nat)
    (choose : Group → Candidate) : Nat :=
  (groups.map (fun g => score g (choose g))).sum

/-- Uniform per-group capacity bounds lift to the complete partition. -/
theorem partition_success_bounded_by_signature_capacities
    (groups : List Group)
    (score : Group → Candidate → Nat)
    (choose : Group → Candidate)
    (capacity : Group → Nat)
    (hCap : ∀ g c, score g c ≤ capacity g) :
    groupSuccessTotal groups score choose ≤
      (groups.map capacity).sum := by
  unfold groupSuccessTotal
  induction groups with
  | nil =>
      simp
  | cons g rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hCap g (choose g)) ih

/-- Every group has n cases. Sum the irreducible shortfalls when its
    exact signature-only capacity is bounded by k ≤ n. -/
theorem signature_shortfalls_add_to_group_sizes
    (groups : List Group)
    (count capacity : Group → Nat)
    (h : ∀ g, capacity g ≤ count g) :
    (groups.map capacity).sum +
      (groups.map (fun g => count g - capacity g)).sum =
      (groups.map count).sum := by
  induction groups with
  | nil =>
      rfl
  | cons g rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have hBound := h g
      omega

/-- These fourteen numbers are the candidate-wise hindsight maxima for
    the source-locked NOR-15C acceptance-signature groups, largest first.
    Their provenance is independently audited in Compactification-Theory. -/
def frozenSignatureCapacities : List Nat :=
  [3, 3, 2, 4, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1]

/-- Sizes of the corresponding frozen NOR-15C signature groups. -/
def frozenSignatureGroupSizes : List Nat :=
  [13, 5, 5, 4, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1]

theorem frozen_group_capacity_sum :
    frozenSignatureCapacities.sum = 25 := by
  decide

theorem frozen_group_source_count :
    frozenSignatureGroupSizes.sum = 40 := by
  decide

/-- The biggest class has thirteen sources, with at most three correct
    under any mask-only constant candidate. -/
theorem largest_mask_class_forces_ten_failures :
    13 - 3 = 10 := by
  decide

#print axioms partition_success_bounded_by_signature_capacities
#print axioms signature_shortfalls_add_to_group_sizes
#print axioms frozen_group_capacity_sum
#print axioms frozen_group_source_count
#print axioms largest_mask_class_forces_ten_failures

end MathCan.NOR15MaskCapacity

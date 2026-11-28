import MathCan.NOR33OverlapMatchedCoverage

/-!
NOR-34: exact eight-atom risk-membership matched attack counts.

A source-public original risk partition consists of eight disjoint
tail/magnitude/lag membership atoms. Each atom j contains n_j possible
changed coordinates and an auditor checks t_j of those. An attacker
draws q_j distinct altered coordinates within that atom. Assuming
the category quotas are fixed, exact conditional misses are the
product of C(n_j-t_j,q_j), from total product of C(n_j,q_j).
This is a finite counting theorem, independent of the likelihood that
any particular source has those quotas.

NOR-33 supplied this identity for two blocks; here arbitrary finite
rosters of blocks and quotas are supported, in particular the eight
three-bit historical-risk categories of NOR-34.

A public category match fixes the attack's pattern quotas; if two
audit policies check equal numbers in every same atom, their finite
conditional detectability is exactly identical. Coarse union-only
matching has no corresponding guarantee, since inspection counts
may differ between atoms within that union.
-/

namespace MathCan.NOR34EightAtomMatchedCoverage

abbrev choose := MathCan.NOR23CoordinateAudit.binomial
abbrev inspectedCount := MathCan.NOR32UnknownSupportCoverage.inspectedCount
def subsetCount (cells : List Bool) (quota : Nat) : Nat :=
  (MathCan.NOR23CoordinateAudit.kSubsets cells quota).length
def cleanSubsetCount (cells : List Bool) (quota : Nat) : Nat :=
  (MathCan.NOR23CoordinateAudit.kSubsets
    (cells.filter (fun flag => !flag)) quota).length

/-- Exact cardinality of all quota-conditioned placement choices over
    arbitrarily many disjoint indexed atoms. Mismatched vector lengths
    have the explicitly empty count zero. -/
def totalPlacements : List (List Bool) → List Nat → Nat
  | [], [] => 1
  | c :: cs, q :: qs => subsetCount c q * totalPlacements cs qs
  | _, _ => 0

/-- Exact cardinality of changes that evade every inspected atom
    position while preserving the fixed quota vector. -/
def missedPlacements : List (List Bool) → List Nat → Nat
  | [], [] => 1
  | c :: cs, q :: qs => cleanSubsetCount c q * missedPlacements cs qs
  | _, _ => 0

def totalBinomial : List (List Bool) → List Nat → Nat
  | [], [] => 1
  | c :: cs, q :: qs => choose c.length q * totalBinomial cs qs
  | _, _ => 0

def missedBinomial : List (List Bool) → List Nat → Nat
  | [], [] => 1
  | c :: cs, q :: qs =>
      choose (c.length - inspectedCount c) q * missedBinomial cs qs
  | _, _ => 0

theorem exact_eight_atom_total_placements
    (cells : List (List Bool)) (quotas : List Nat) :
    totalPlacements cells quotas = totalBinomial cells quotas := by
  induction cells generalizing quotas with
  | nil =>
      cases quotas <;> rfl
  | cons cell rest ih =>
      cases quotas with
      | nil => rfl
      | cons quota qs =>
          have hhead : subsetCount cell quota = choose cell.length quota := by
            simpa [subsetCount, choose,
                    MathCan.NOR32UnknownSupportCoverage.candidateAttacks,
                    MathCan.NOR32UnknownSupportCoverage.choose] using
              (congrArg Prod.snd
                (MathCan.NOR32UnknownSupportCoverage.exact_unknown_support_attack_miss_and_total
                  cell quota))
          simp only [totalPlacements, totalBinomial]
          rw [hhead, ih]

theorem exact_eight_atom_missed_placements
    (cells : List (List Bool)) (quotas : List Nat) :
    missedPlacements cells quotas = missedBinomial cells quotas := by
  induction cells generalizing quotas with
  | nil =>
      cases quotas <;> rfl
  | cons cell rest ih =>
      cases quotas with
      | nil => rfl
      | cons quota qs =>
          have hhead : cleanSubsetCount cell quota =
              choose (cell.length - inspectedCount cell) quota := by
            simpa [cleanSubsetCount, choose, inspectedCount,
                    MathCan.NOR32UnknownSupportCoverage.undetectedAttackPlacements,
                    MathCan.NOR32UnknownSupportCoverage.choose,
                    MathCan.NOR32UnknownSupportCoverage.inspectedCount] using
              (congrArg Prod.fst
                (MathCan.NOR32UnknownSupportCoverage.exact_unknown_support_attack_miss_and_total
                  cell quota))
          simp only [missedPlacements, missedBinomial]
          rw [hhead, ih]

theorem eight_atom_hypergeometric_count_pair
    (cells : List (List Bool)) (quotas : List Nat) :
    (missedPlacements cells quotas, totalPlacements cells quotas) =
      (missedBinomial cells quotas, totalBinomial cells quotas) := by
  rw [exact_eight_atom_missed_placements, exact_eight_atom_total_placements]

/-- Equal atom population and inspected-count vectors give identical
    conditional quota-matched attack numerator and denominator counts. -/
theorem matched_atom_statistics_give_equal_count_pair
    (first second : List (List Bool))
    (quotas : List Nat)
    (sameLengths : first.map List.length = second.map List.length)
    (sameChecked : first.map inspectedCount = second.map inspectedCount) :
    (missedPlacements first quotas, totalPlacements first quotas) =
      (missedPlacements second quotas, totalPlacements second quotas) := by
  have hbins :
      (missedBinomial first quotas, totalBinomial first quotas) =
        (missedBinomial second quotas, totalBinomial second quotas) := by
    induction first generalizing second quotas with
    | nil =>
        cases second with
        | nil => cases quotas <;> rfl
        | cons s ss => cases sameLengths
    | cons f fs ih =>
        cases second with
        | nil => cases sameLengths
        | cons s ss =>
            have hlen : f.length = s.length := by
              have h := congrArg List.head? sameLengths
              simpa using h
            have hchecked : inspectedCount f = inspectedCount s := by
              have h := congrArg List.head? sameChecked
              simpa using h
            have htail : fs.map List.length = ss.map List.length := by
              have h := congrArg List.tail sameLengths
              simpa using h
            have htailchecked : fs.map inspectedCount = ss.map inspectedCount := by
              have h := congrArg List.tail sameChecked
              simpa using h
            cases quotas with
            | nil => rfl
            | cons q qs =>
                have hrecur := ih ss qs htail htailchecked
                have hm := congrArg Prod.fst hrecur
                have ht := congrArg Prod.snd hrecur
                apply Prod.ext
                · simpa [missedBinomial, hlen, hchecked] using
                    (congrArg
                      (fun n => choose (s.length - inspectedCount s) q * n) hm)
                · simpa [totalBinomial, hlen] using
                    (congrArg (fun n => choose s.length q * n) ht)
  calc
    (missedPlacements first quotas, totalPlacements first quotas) =
        (missedBinomial first quotas, totalBinomial first quotas) :=
      eight_atom_hypergeometric_count_pair first quotas
    _ = (missedBinomial second quotas, totalBinomial second quotas) := hbins
    _ = (missedPlacements second quotas, totalPlacements second quotas) :=
      (eight_atom_hypergeometric_count_pair second quotas).symm

/-- For any finite roster of quota draws, matching all eight atom
    inspection counts guarantees the same exact missed and total pairs
    for every draw in the roster. This is the algebra behind
    standardizing over a fixed distribution of eight-pattern quotas. -/
theorem finite_quota_mixture_invariant_under_full_atom_matching
    (first second : List (List Bool))
    (quotas : List (List Nat))
    (sameLengths : first.map List.length = second.map List.length)
    (sameChecked : first.map inspectedCount = second.map inspectedCount) :
    quotas.map (fun q =>
      (missedPlacements first q, totalPlacements first q)) =
    quotas.map (fun q =>
      (missedPlacements second q, totalPlacements second q)) := by
  apply List.map_congr_left
  intro q _
  exact matched_atom_statistics_give_equal_count_pair
    first second q sameLengths sameChecked

/-- A coarse total-union inspection count is generally insufficient:
    inspecting atom A or B once yields different misses for an attack
    that must alter atom A. Both auditors inspect one position overall. -/
theorem coarse_union_count_is_insufficient :
    missedPlacements [[true, false, false, false],
      [false, false, false, false]] [1, 0] = 3 ∧
    missedPlacements [[false, false, false, false],
      [true, false, false, false]] [1, 0] = 4 := by
  decide

#print axioms exact_eight_atom_total_placements
#print axioms exact_eight_atom_missed_placements
#print axioms eight_atom_hypergeometric_count_pair
#print axioms matched_atom_statistics_give_equal_count_pair
#print axioms finite_quota_mixture_invariant_under_full_atom_matching
#print axioms coarse_union_count_is_insufficient

end MathCan.NOR34EightAtomMatchedCoverage

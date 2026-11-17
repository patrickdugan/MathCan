import MathCan.NOR38UniformAuditMaximin

/-!
NOR-40: fourth-smallest singleton exposure as a sound global CAL lower
bound for any four-distinct-coordinate precommitted attack support.

Given the list of singleton exposures sorted in nondecreasing order,
any four distinct coordinate ranks must contain a rank >=3. The union
detection score of a four-coordinate attack is at least the score of
each selected singleton when component audit weights are nonnegative.
Therefore the fourth-smallest singleton cost is at most every feasible
four-coordinate union score.

This is a ranking/coverage lemma for the optimizer's integer CAL
objective. It neither certifies the actual full-domain minimum nor
constrains out-of-sample EVAL detection. Ranking correspondence and
componentwise monotone union counts are checked by the NOR40 Python
source and its independent receipt replay.
-/

namespace MathCan.NOR40SingletonBracket

/-- Four pairwise-distinct nonnegative ranks cannot all lie within
    the first three positions 0, 1, 2. -/
theorem four_distinct_ranks_have_one_at_least_three
    (i j k l : Nat)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    3 ≤ i ∨ 3 ≤ j ∨ 3 ≤ k ∨ 3 ≤ l := by
  omega

/-- If scores are indexed by their nondecreasing rank, and a chosen
    size-four support has union-detection score at least each of its
    singleton scores, the fourth-lowest singleton is a global lower
    bound on that chosen support's CAL objective. -/
theorem fourth_singleton_bounds_every_four_support
    (singletonByRank : Nat → Nat)
    (i j k l fourUnionScore : Nat)
    (hordered : ∀ a b : Nat, a ≤ b →
      singletonByRank a ≤ singletonByRank b)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hi : singletonByRank i ≤ fourUnionScore)
    (hj : singletonByRank j ≤ fourUnionScore)
    (hk : singletonByRank k ≤ fourUnionScore)
    (hl : singletonByRank l ≤ fourUnionScore) :
    singletonByRank 3 ≤ fourUnionScore := by
  rcases four_distinct_ranks_have_one_at_least_three
      i j k l hij hik hil hjk hjl hkl with
    h | h | h | h
  · exact (hordered 3 i h).trans hi
  · exact (hordered 3 j h).trans hj
  · exact (hordered 3 k h).trans hk
  · exact (hordered 3 l h).trans hl

/-- Multiplying component detection counts by a nonnegative integer
    policy weight preserves the inclusion-induced singleton bound. -/
theorem nonnegative_policy_weight_preserves_singleton_coverage
    (weight singletonCovered unionCovered : Nat)
    (subsetExposure : singletonCovered ≤ unionCovered) :
    weight * singletonCovered ≤ weight * unionCovered := by
  exact Nat.mul_le_mul_left weight subsetExposure

/-- Any source-public attack construction yielding a feasible score U
    bounds the unknown global CAL minimum above; combining it with the
    fourth-singleton lower bound produces a sound finite bracket.
    The premises are checked on the full coordinate domain separately. -/
theorem global_cal_optimum_lies_in_bracket
    (fourthSingleton actualGlobalMin bestFeasible : Nat)
    (hLower : fourthSingleton ≤ actualGlobalMin)
    (hUpper : actualGlobalMin ≤ bestFeasible) :
    fourthSingleton ≤ actualGlobalMin ∧
      actualGlobalMin ≤ bestFeasible := by
  exact ⟨hLower,hUpper⟩

#print axioms four_distinct_ranks_have_one_at_least_three
#print axioms fourth_singleton_bounds_every_four_support
#print axioms nonnegative_policy_weight_preserves_singleton_coverage
#print axioms global_cal_optimum_lies_in_bracket

end MathCan.NOR40SingletonBracket

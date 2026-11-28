import MathCan.NOR23CoordinateAudit

/-!
# NOR-24: sequential exact witnesses and conditional attack-set counts

A public-only candidate can use an authentic coefficient witness one
coordinate at a time. If two possible worlds agree on all values
revealed so far, the resulting witness transcript is identical.
Any next-query rule depending on that transcript must make the same
choice. The first discrepancy is the only observation that separates
these two worlds in this exact-value protocol.

The finite sequential no-hit likelihood of a fixed-radius attack in
an explicitly declared support is the number of radius-r subsets of
the still-unchecked positions divided by all radius-r subsets of the
support. Exact counts use the original NOR-23 binomial enumerator.
These results are conditional on a declared support and authentic
witnesses; the applied controller's training, source distribution,
sample independence and computation time are empirical questions.
-/

namespace MathCan.NOR24SequentialWitness

universe u
variable {Coordinate : Type u}

/-- A sequential verifier sees the exact value at each queried
coordinate, in order, assuming an honest target witness. -/
def readTranscript (probes : List Coordinate)
    (target : Coordinate → Int) : List (Coordinate × Int) :=
  probes.map (fun i => (i,target i))

/-- A clean transcript from two worlds is identical whenever the
targets agree on all previously queried coordinates. -/
theorem checked_equal_targets_have_equal_transcripts
    (probes : List Coordinate)
    (a b : Coordinate → Int)
    (h : MathCan.NOR23CoordinateAudit.agreesOn probes a b) :
    readTranscript probes a = readTranscript probes b := by
  unfold readTranscript
  apply List.map_congr_left
  intro i hi
  exact congrArg (fun v => (i, v)) (h i hi)

/-- A deterministic adaptive selector taking only the public state
and the revealed transcript chooses the same next coordinate in any
two worlds with identical clean transcripts. -/
theorem identical_clean_history_forces_same_next_probe
    {Public : Type u}
    (policy : Public → List (Coordinate × Int) → Coordinate)
    (observation : Public)
    (probes : List Coordinate)
    (a b : Coordinate → Int)
    (h : MathCan.NOR23CoordinateAudit.agreesOn probes a b) :
    policy observation (readTranscript probes a) =
      policy observation (readTranscript probes b) := by
  rw [checked_equal_targets_have_equal_transcripts probes a b h]

/-- If altered target coefficients can occur only in declared support
S, an audit that inspects solely outside S receives a clean transcript. -/
theorem audit_outside_attack_support_produces_no_discrepancy
    (checked support : List Coordinate)
    (candidate altered : Coordinate → Int)
    (outside : ∀ i ∈ checked, i ∉ support)
    (supportOnly : ∀ i, i ∉ support → candidate i = altered i) :
    MathCan.NOR23CoordinateAudit.agreesOn checked candidate altered := by
  intro i hi
  exact supportOnly i (outside i hi)

/-- In a known finite attack support, remove all already inspected
coordinates before forming the next uniform attack subset count.
List indices represent distinct positions. -/
def uncheckedSupport (support checked : List Nat) : List Nat :=
  support.filter (fun i => !decide (i ∈ checked))

/-- Number of possible radius-r attack subsets remaining after clean
queries equals choose(number of unchecked support positions,r). -/
theorem exact_nohit_attack_set_count
    (support checked : List Nat) (radius : Nat) :
    (MathCan.NOR23CoordinateAudit.kSubsets
      (uncheckedSupport support checked) radius).length =
    MathCan.NOR23CoordinateAudit.binomial
      (uncheckedSupport support checked).length radius := by
  exact MathCan.NOR23CoordinateAudit.k_subset_count_is_binomial
    (uncheckedSupport support checked) radius

/-- When the possible attack support is divided into inspected and
uninspected portions, zero-detection likelihood is the ratio of these
exact counts, subject to uniform fixed-radius attack sampling. -/
def unnormalizedNoHitCount (support checked : List Nat) (radius : Nat) : Nat :=
  MathCan.NOR23CoordinateAudit.binomial
    (uncheckedSupport support checked).length radius

theorem nohit_count_matches_exhaustive_attack_subsets
    (support checked : List Nat) (radius : Nat) :
    unnormalizedNoHitCount support checked radius =
      (MathCan.NOR23CoordinateAudit.kSubsets
        (uncheckedSupport support checked) radius).length := by
  exact (exact_nohit_attack_set_count support checked radius).symm

/-- Counting attacks after an additional exact clean query splits all
radius-(r+1) configurations into those including that coordinate and
those excluding it. This is the Pascal identity used to update the
posterior family likelihood without a target oracle. -/
theorem one_step_hit_miss_count_partition
    (remaining radius : Nat) :
    MathCan.NOR23CoordinateAudit.binomial (remaining+1) (radius+1) =
      MathCan.NOR23CoordinateAudit.binomial remaining radius +
      MathCan.NOR23CoordinateAudit.binomial remaining (radius+1) := by
  rfl

/-- Every alternative future agreeing with the original on the
complete inspected transcript makes the next adaptive query identical,
regardless of the internal computation performed by the policy. -/
theorem modified_future_can_preserve_adaptive_next_probe
    {Public : Type u}
    (policy : Public → List (Coordinate × Int) → Coordinate)
    (observation : Public)
    (checked : List Coordinate)
    (candidate altered : Coordinate → Int)
    (h : MathCan.NOR23CoordinateAudit.agreesOn checked candidate altered) :
    policy observation (readTranscript checked candidate) =
      policy observation (readTranscript checked altered) :=
  identical_clean_history_forces_same_next_probe
    policy observation checked candidate altered h

#print axioms checked_equal_targets_have_equal_transcripts
#print axioms identical_clean_history_forces_same_next_probe
#print axioms audit_outside_attack_support_produces_no_discrepancy
#print axioms exact_nohit_attack_set_count
#print axioms nohit_count_matches_exhaustive_attack_subsets
#print axioms one_step_hit_miss_count_partition
#print axioms modified_future_can_preserve_adaptive_next_probe

end MathCan.NOR24SequentialWitness

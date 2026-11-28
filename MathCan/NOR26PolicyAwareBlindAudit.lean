import MathCan.NOR25UniformReserve

/-!
# NOR-26: unconditional-over-targeted-prefix blind audit floor

NOR-25 proved exact residual hypergeometric sample counts for one
targeted prefix. NOR-26 allows a policy-aware adversary to choose its
fixed alteration set *after learning the public policy*, then requires
that set to remain fixed before the actual audit random coins.

We formalize a finite distribution of arbitrary targeted-prefix
outcomes. In each outcome either the risk prefix already discovers a
changed coordinate, or the uninspected population has a common size N
and exactly r changed coordinates. A uniformly random reserve of size
u in that population has at most C(N-r,u) undetected subset schedules.
Summing across ANY finite targeted-prefix distribution preserves this
bound for the entire cross-play population.

The prefix outcomes can include arbitrary, even adversarially known,
public-risk selection logic. What matters is independence of the
subsequent uniform reserve from the fixed alteration set.

This theorem bounds finite counts. Uniform probability, a concealed
sample realization and an honest external coefficient witness are
assumptions in the applied NOR-26 study. Revealing the actual complete
schedule revives the constructive NOR-25 evasion.
-/

namespace MathCan.NOR26PolicyAwareBlindAudit

abbrev binomial := MathCan.NOR23CoordinateAudit.binomial
abbrev missedReserveCount := MathCan.NOR25UniformReserve.missedReserveCount

/-- The observable state of one public targeted-prefix decision.
    Its residual mask covers all unchecked future coefficients. -/
structure PrefixOutcome where
  targetedHit : Bool
  residual : List Bool

/-- Exact number of undetected uniform-reserve position-subset schedules
    across a finite roster of targeted-prefix outcomes. -/
def totalMisses (outcomes : List PrefixOutcome) (reserve : Nat) : Nat :=
  (outcomes.map (fun p =>
    missedReserveCount p.targetedHit p.residual reserve)).sum

/-- A fixed prior attack of radius r, after any targeted prefix,
    either has already been detected or leaves exactly r altered
    positions among the N unchecked coordinates. -/
def fixedBlindRadius
    (N r : Nat) (p : PrefixOutcome) : Prop :=
  p.residual.length = N ∧
    (p.targetedHit = false →
      (p.residual.filter (fun b => b)).length = r)

/-- The same finite cap applies to every targeted-prefix case, however
    the targeted part of the verifier chose its positions. -/
theorem any_prefix_conditional_misses_bounded
    (N r reserve : Nat)
    (p : PrefixOutcome)
    (h : fixedBlindRadius N r p) :
    missedReserveCount p.targetedHit p.residual reserve ≤
      binomial (N-r) reserve := by
  rcases h with ⟨hsize, hcount⟩
  cases hp : p.targetedHit with
  | true =>
      simp [missedReserveCount,
        MathCan.NOR25UniformReserve.missedReserveCount,
        binomial]
  | false =>
      have hb :=
        MathCan.NOR25UniformReserve.uniform_reserve_miss_count_bounded
          false p.residual reserve
      have hc : (p.residual.filter (fun b => b)).length = r :=
        hcount hp
      simpa [missedReserveCount, binomial, hsize, hc] using hb

/-- A policy can randomize over any finite list of prefix decisions.
    Every prefix has exactly C(N,reserve) possible equally weighted
    random-reserve position schedules. The total number of misses
    is bounded by the number of prefixes times C(N-r,reserve).
    Repeated prefixes encode rational policy weights by multiplicity. -/
theorem policy_aware_fixed_attack_mixture_bound
    (N r reserve : Nat)
    (outcomes : List PrefixOutcome)
    (valid : ∀ p ∈ outcomes, fixedBlindRadius N r p) :
    totalMisses outcomes reserve ≤
      outcomes.length * binomial (N-r) reserve := by
  induction outcomes with
  | nil =>
      simp [totalMisses]
  | cons p rest ih =>
      have hhead : fixedBlindRadius N r p :=
        valid p (by simp)
      have htail : ∀ v ∈ rest, fixedBlindRadius N r v := by
        intro v hv
        exact valid v (by simp [hv])
      have hb := any_prefix_conditional_misses_bounded N r reserve p hhead
      have ht := ih htail
      unfold totalMisses at ht
      simp only [totalMisses, List.map_cons, List.sum_cons,
        List.length_cons, Nat.succ_mul]
      omega

/-- After conditioning on the prefix already detecting an altered
    coordinate, all possible reserve schedules detect the attack. -/
theorem prefix_hit_has_no_false_acceptance
    (remaining : List Bool) (reserve : Nat) :
    missedReserveCount true remaining reserve = 0 := by
  rfl

/-- Even when the attacker chooses the alteration knowing the full
    public policy, an actual revealed audit schedule has a stronger
    information boundary: if one unchecked location remains, a distinct
    hidden target gives the same exact-value transcript. -/
theorem schedule_visible_attack_remains_undetectable
    {Coordinate : Type}
    (checked : List Coordinate)
    (target : Coordinate → Int)
    (existsUnseen : ∃ i : Coordinate, i ∉ checked) :
    ∃ altered : Coordinate → Int,
      altered ≠ target ∧
      MathCan.NOR24SequentialWitness.readTranscript checked target =
        MathCan.NOR24SequentialWitness.readTranscript checked altered := by
  exact MathCan.NOR25UniformReserve.schedule_visible_attacker_has_identical_transcript
    checked target existsUnseen

#print axioms any_prefix_conditional_misses_bounded
#print axioms policy_aware_fixed_attack_mixture_bound
#print axioms prefix_hit_has_no_false_acceptance
#print axioms schedule_visible_attack_remains_undetectable

end MathCan.NOR26PolicyAwareBlindAudit

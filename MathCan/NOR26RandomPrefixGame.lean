import MathCan.NOR25UniformReserve

/-!
# NOR-26: policy-aware blind attackers and random targeted-prefix mixtures

Let a schedule-blind radius-r attacker fix altered coefficients after observing
the auditor's public *distribution*, but before the actual prefix and reserve
samples are drawn. For each targeted prefix T of length t, the external exact
witness either detects an alteration immediately, or leaves r alterations in
the N=m-t unchecked coordinates. Given a uniform u-subset of those coordinates,
exact missed-reserve enumeration is C(N-r,u) when all r changes survived the
prefix; it is zero when the targeted prefix already encountered a change.

Summing this conditional count over any finite collection of candidate risk
prefixes bounds the complete mixture's number of undetected challenges by
(number of prefixes) * C(N-r,u). This counting bound is independent of the
attacker's calibration computation, internal selection rule, source prior,
and distribution of risk-targeted prefixes (uniform mixing can represent
general rational mixtures by duplicating prefix entries).

Interpretation as probability requires the attacker to commit before
independent exact uniform reserve sampling and an authentic external witness.
A revealed completed schedule still admits an altered target with the same
witness transcript, as formalized in NOR-25.
-/

namespace MathCan.NOR26RandomPrefixGame

open MathCan.NOR23CoordinateAudit
open MathCan.NOR25UniformReserve

/-- One hypothetical public-risk prefix, represented by whether it has
already hit the fixed attack and the Boolean alteration mask on the
remaining N unchecked coordinates. -/
abbrev ResidualWorld := Bool × List Bool

/-- Every sample of a prefix remains in the same coordinate universe.
If the targeted prefix misses the attack, the residual mask has exactly
r changed positions. -/
def validResidual (N r : Nat) (world : ResidualWorld) : Prop :=
  world.2.length = N ∧
    (world.1 = false → (world.2.filter (fun b => b)).length = r)

/-- The maximum number of missed size-u uniform reserves in any
conditional targeted-prefix world is C(N-r,u). -/
theorem each_public_prefix_has_bounded_misses
    (world : ResidualWorld) (N r reserve : Nat)
    (h : validResidual N r world) :
    missedReserveCount world.1 world.2 reserve ≤
      MathCan.NOR23CoordinateAudit.binomial (N-r) reserve := by
  rcases world with ⟨hit, rest⟩
  rcases h with ⟨hsize, hcount⟩
  cases hit with
  | false =>
      change
        (kSubsets (rest.filter (fun b => !b)) reserve).length ≤
          MathCan.NOR23CoordinateAudit.binomial (N-r) reserve
      rw [fixed_attack_undetected_challenge_count rest reserve]
      rw [hsize, hcount rfl]
      exact le_rfl
  | true =>
      simp [missedReserveCount]

/-- The finite challenge ensemble is all uniform-reserve choices made
after the public-risk prefix is selected, counted with multiplicity.
A rational prefix distribution can be encoded by repeated worlds. -/
def totalMissedReserves (worlds : List ResidualWorld) (reserve : Nat) : Nat :=
  (worlds.map (fun w => missedReserveCount w.1 w.2 reserve)).sum

/-- Crucial new bound: any finite mixture of publicly chosen risk
prefixes preserves the hypergeometric upper bound on misses, even when
the attacker optimized its fixed changes against that mixture. -/
theorem random_prefix_mixture_miss_bound
    (worlds : List ResidualWorld) (N r reserve : Nat)
    (h : ∀ w ∈ worlds, validResidual N r w) :
    totalMissedReserves worlds reserve ≤
      worlds.length * MathCan.NOR23CoordinateAudit.binomial (N-r) reserve := by
  induction worlds with
  | nil =>
      simp [totalMissedReserves]
  | cons w rest ih =>
      have hhead : validResidual N r w := h w (by simp)
      have htail : ∀ x ∈ rest, validResidual N r x := by
        intro x hx
        exact h x (List.mem_cons_of_mem w hx)
      have hb := each_public_prefix_has_bounded_misses w N r reserve hhead
      have ht := ih htail
      change
        missedReserveCount w.1 w.2 reserve +
          totalMissedReserves rest reserve ≤
        (rest.length+1) * MathCan.NOR23CoordinateAudit.binomial (N-r) reserve
      simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using Nat.add_le_add hb ht

/-- A policy's state can include an arbitrary calibration transcript,
public model state, score table and random seed distribution. Applying
the policy to that information cannot change the universal bound on
independent uniform-reserve misses. -/
theorem calibrated_policy_mixture_bound
    {Calibration : Type}
    (policy : Calibration → List ResidualWorld)
    (calibration : Calibration)
    (N r reserve : Nat)
    (h : ∀ w ∈ policy calibration, validResidual N r w) :
    totalMissedReserves (policy calibration) reserve ≤
      (policy calibration).length * MathCan.NOR23CoordinateAudit.binomial (N-r) reserve := by
  exact random_prefix_mixture_miss_bound
    (policy calibration) N r reserve h

/-- For a fixed targeted-prefix distribution, the total count of all
possible reserves is a product because every prefix has N unchecked
coordinates, and every coordinate subset has the same unit weight. -/
theorem full_mixture_schedule_count
    (worlds : List ResidualWorld) (N reserve : Nat)
    (h : ∀ w ∈ worlds, w.2.length = N) :
    ((worlds.map (fun w => allReserveCount w.2 reserve)).sum) =
      worlds.length * MathCan.NOR23CoordinateAudit.binomial N reserve := by
  induction worlds with
  | nil =>
      simp
  | cons w rest ih =>
      have hw : w.2.length = N := h w (by simp)
      have ht : ∀ x ∈ rest, x.2.length = N := by
        intro x hx
        exact h x (List.mem_cons_of_mem w hx)
      have hsub := ih ht
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [show allReserveCount w.2 reserve = MathCan.NOR23CoordinateAudit.binomial N reserve by
        simpa [allReserveCount, hw] using
          (total_k_coordinate_challenges w.2 reserve)]
      rw [hsub]
      simp [Nat.succ_mul, Nat.add_comm]

#print axioms each_public_prefix_has_bounded_misses
#print axioms random_prefix_mixture_miss_bound
#print axioms calibrated_policy_mixture_bound
#print axioms full_mixture_schedule_count

end MathCan.NOR26RandomPrefixGame

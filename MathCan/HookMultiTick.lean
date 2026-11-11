import MathCan.V4Transient

/-!
# CHTR-10: hook-return splits and multi-tick accounting

A small proof kernel for signed caller/hook/pool deltas and tick-level input
accounting. The bytecode observation, Keccak slots, tick prices and rounding
are checked by the paired Python and pinned Foundry executions. This module
proves generic integer conservation consequences, independent of any EVM claim.
-/

namespace MathCan.HookMultiTick

/-- A pool delta is distributed across the caller and the hook. -/
structure DeltaSplit where
  pool : Int
  caller : Int
  hook : Int
  deriving DecidableEq, Repr

def WellSplit (s : DeltaSplit) : Prop := s.pool = s.caller + s.hook

/-- Source-inspired split: caller receives the pool delta minus the hook delta. -/
def distribute (pool hook : Int) : DeltaSplit :=
  ⟨pool, pool - hook, hook⟩

theorem distribute_sound (pool hook : Int) : WellSplit (distribute pool hook) := by
  simp [WellSplit, distribute]

/-- Every per-currency signed split conserves its total when physical custody
    changes by the opposite of the pool delta. -/
theorem three_account_conservation (split : DeltaSplit)
    (h : WellSplit split) : split.caller + split.hook - split.pool = 0 := by
  dsimp [WellSplit] at h
  omega

/-- A hook returning positive amount of the input currency adds that amount
    to the original (negative) exact-input specification before Pool.swap. -/
theorem before_swap_exact_input (requested specified poolAmount : Int)
    (h : poolAmount = requested + specified) :
    requested = poolAmount - specified := by
  omega

/-- Restoring the original caller debit follows from the hook's
    specified-currency credit, independently of the pool's output. -/
theorem specified_credit_restores_debit
    (requested specified poolAmount callerAmount : Int)
    (hPool : poolAmount = requested + specified)
    (hCaller : callerAmount = poolAmount - specified) :
    callerAmount = requested := by
  omega

/-- The pre-swap and post-swap unspecified credits combine into one hook
    claim, with the caller receiving the remaining pool output. -/
theorem unspecified_split
    (poolOutput beforeUnspecified afterUnspecified hookOutput callerOutput : Int)
    (hHook : hookOutput = beforeUnspecified + afterUnspecified)
    (hCaller : callerOutput = poolOutput - hookOutput) :
    poolOutput = callerOutput + beforeUnspecified + afterUnspecified := by
  omega

/-- Aggregate accounting over a sequence of signed pool/caller/hook entries. -/
def sumPool (xs : List DeltaSplit) : Int := (xs.map (·.pool)).sum
def sumCaller (xs : List DeltaSplit) : Int := (xs.map (·.caller)).sum
def sumHook (xs : List DeltaSplit) : Int := (xs.map (·.hook)).sum

/-- Conservation is stable under arbitrary finite concatenations of correctly
    split action receipts, including adaptive selections of actions. -/
theorem route_conservation (xs : List DeltaSplit)
    (h : ∀ x, x ∈ xs → WellSplit x) :
    sumPool xs = sumCaller xs + sumHook xs := by
  induction xs with
  | nil => simp [sumPool, sumCaller, sumHook]
  | cons x rest ih =>
    have hx : WellSplit x := h x (List.mem_cons_self)
    have hr : ∀ y, y ∈ rest → WellSplit y := by
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)
    have hrest := ih hr
    simp only [sumPool, sumCaller, sumHook, List.map_cons, List.sum_cons] at *
    dsimp [WellSplit] at hx
    omega

/-- One tick step records input delivered to the pool, paid swap fee, and
    output from the pool, all in atomic token units. -/
structure TickStep where
  netInput : Int
  fee : Int
  output : Int
  deriving DecidableEq, Repr

def totalGross (xs : List TickStep) : Int := (xs.map (fun s => s.netInput + s.fee)).sum
def totalNet (xs : List TickStep) : Int := (xs.map (·.netInput)).sum
def totalFee (xs : List TickStep) : Int := (xs.map (·.fee)).sum
def totalOutput (xs : List TickStep) : Int := (xs.map (·.output)).sum

/-- Input plus fee is conserved exactly across every split tick, even when
    each step uses a different active liquidity value. -/
theorem gross_input_partition (xs : List TickStep) :
    totalGross xs = totalNet xs + totalFee xs := by
  induction xs with
  | nil => simp [totalGross, totalNet, totalFee]
  | cons x rest ih =>
    simp only [totalGross, totalNet, totalFee, List.map_cons, List.sum_cons] at *
    omega

/-- Output accounting for two adjacent tick paths is additive. -/
theorem outputs_append (a b : List TickStep) :
    totalOutput (a ++ b) = totalOutput a + totalOutput b := by
  simp [totalOutput, List.map_append, List.sum_append]

/-- The total output allocated to hook and caller equals the sum of
    individual tick outputs when the two deltas are sourced from that swap. -/
theorem output_with_hook
    (xs : List TickStep) (caller hook : Int)
    (h : caller + hook = totalOutput xs) :
    totalOutput xs - caller = hook := by
  omega

/-- Reusing the established finite-support count theorem: a source-observed
    zero counter certifies every listed caller/hook currency delta is zero. -/
theorem zero_counter_clears_observed_pairs
    (deltaSlots : List Int) (reportedCount : Int)
    (hExact : reportedCount = MathCan.V4Transient.count deltaSlots)
    (hZero : reportedCount = 0) :
    ∀ x, x ∈ deltaSlots → x = 0 := by
  exact MathCan.V4Transient.lock_zero_count deltaSlots reportedCount hExact hZero

#print axioms distribute_sound
#print axioms three_account_conservation
#print axioms before_swap_exact_input
#print axioms specified_credit_restores_debit
#print axioms unspecified_split
#print axioms route_conservation
#print axioms gross_input_partition
#print axioms outputs_append
#print axioms output_with_hook
#print axioms zero_counter_clears_observed_pairs

end MathCan.HookMultiTick

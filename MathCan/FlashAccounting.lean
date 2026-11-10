import MathCan.Settlement

/-!
# CHTR-06: an abstract integer flash-accounting kernel

This module establishes conservation for a *declared* abstract transition
system. A proof that a particular deployed EVM hook refines these operations
requires separate bytecode/call-frame/balance evidence. The Python trace
verifier records the corresponding integer transition receipts.

`FlashBook` is the aggregate of one currency across all accounts and pools.
The invariant is

  manager vault = virtual pool amounts + redeemable ERC6909-like claims
                + signed transient caller deltas + unallocated surplus.

Each operation preserves that equality. Two currencies are simply two copies.
-/

namespace MathCan.FlashAccounting

structure FlashBook where
  vault : Int
  pools : Int
  claims : Int
  deltas : Int
  surplus : Int
  deriving Repr, DecidableEq

/-- Aggregate backing equation for one currency. -/
def Backed (s : FlashBook) : Prop :=
  s.vault = s.pools + s.claims + s.deltas + s.surplus

/-- A pool allocation changes the caller's transient obligation oppositely. -/
def poolDelta (s : FlashBook) (amount : Int) : FlashBook :=
  { s with pools := s.pools + amount, deltas := s.deltas - amount }

/-- Direct ERC20 transfer into manager custody enters unallocated surplus. -/
def deposit (s : FlashBook) (amount : Int) : FlashBook :=
  { s with vault := s.vault + amount, surplus := s.surplus + amount }

/-- Direct transfer out of manager custody debits unallocated surplus. -/
def rawWithdrawal (s : FlashBook) (amount : Int) : FlashBook :=
  { s with vault := s.vault - amount, surplus := s.surplus - amount }

/-- `settle` moves deposited surplus into a caller's positive delta. -/
def settle (s : FlashBook) (amount : Int) : FlashBook :=
  { s with deltas := s.deltas + amount, surplus := s.surplus - amount }

/-- `take` moves custody to a recipient, decreasing the caller's delta. -/
def take (s : FlashBook) (amount : Int) : FlashBook :=
  { s with vault := s.vault - amount, deltas := s.deltas - amount }

/-- ERC6909-like mint changes the outstanding liability and caller delta. -/
def mintClaim (s : FlashBook) (amount : Int) : FlashBook :=
  { s with claims := s.claims + amount, deltas := s.deltas - amount }

/-- ERC6909-like burn extinguishes a liability and credits the caller. -/
def burnClaim (s : FlashBook) (amount : Int) : FlashBook :=
  { s with claims := s.claims - amount, deltas := s.deltas + amount }

/-- Exact positive delta forfeiture transfers the benefit to surplus. -/
def clear (s : FlashBook) (amount : Int) : FlashBook :=
  { s with deltas := s.deltas - amount, surplus := s.surplus + amount }

/-- Frame rollback restores the checkpoint, including transient deltas. -/
def revertFrame (checkpoint _attempted : FlashBook) : FlashBook := checkpoint

/-- A conservative abstract opcode vocabulary. -/
inductive Op where
  | pool (amount : Int)
  | deposit (amount : Int)
  | rawWithdrawal (amount : Int)
  | settle (amount : Int)
  | take (amount : Int)
  | mintClaim (amount : Int)
  | burnClaim (amount : Int)
  | clear (amount : Int)
  deriving Repr, DecidableEq

def apply (op : Op) (s : FlashBook) : FlashBook :=
  match op with
  | .pool n => poolDelta s n
  | .deposit n => deposit s n
  | .rawWithdrawal n => rawWithdrawal s n
  | .settle n => settle s n
  | .take n => take s n
  | .mintClaim n => mintClaim s n
  | .burnClaim n => burnClaim s n
  | .clear n => clear s n

/-- Every declared opcode preserves the aggregate backing identity. -/
theorem backed_apply (op : Op) (s : FlashBook) (h : Backed s) :
    Backed (apply op s) := by
  cases op <;> simp [apply, Backed, poolDelta, deposit,
    rawWithdrawal, settle, take, mintClaim, burnClaim, clear] at * <;> omega

/-- Left-to-right execution of a finite abstract trace. -/
def run (s : FlashBook) : List Op → FlashBook
  | [] => s
  | op :: rest => run (apply op s) rest

/-- Conservation holds along arbitrary finite action words. -/
theorem backed_run (s : FlashBook) (h : Backed s) (actions : List Op) :
    Backed (run s actions) := by
  induction actions generalizing s with
  | nil => simpa [run] using h
  | cons op rest ih =>
      simpa [run] using ih (apply op s) (backed_apply op s h)

/-- At lock, zero transient deltas and nonnegative surplus imply vault backing
    for the pool plus outstanding redeemable claims. -/
theorem terminal_vault_solvency (s : FlashBook)
    (h : Backed s) (settled : s.deltas = 0) (safety : 0 ≤ s.surplus) :
    s.pools + s.claims ≤ s.vault := by
  unfold Backed at h
  omega

/-- Claim issuance must consume an equal amount of caller delta. -/
theorem mint_claim_neutral (s : FlashBook) (amount : Int) :
    (mintClaim s amount).claims + (mintClaim s amount).deltas =
      s.claims + s.deltas := by
  simp [mintClaim]
  omega

/-- Exact clearing shifts a positive caller claim into surplus. -/
theorem clear_neutral (s : FlashBook) (amount : Int) :
    (clear s amount).deltas + (clear s amount).surplus =
      s.deltas + s.surplus := by
  simp [clear]
  omega

/-- Call-frame revert restores both the accounting invariant and the original
    state, independently of the uncommitted nested trace. -/
theorem revert_restores_backing (checkpoint attempted : FlashBook)
    (h : Backed checkpoint) : Backed (revertFrame checkpoint attempted) := by
  simpa [revertFrame] using h

/-- A claim transfer between registered holders conserves aggregate liabilities. -/
theorem claim_transfer_conservation (fromBal toBal amount : Int) :
    (fromBal - amount) + (toBal + amount) = fromBal + toBal := by
  omega

/-- A physical transfer between two registered accounts conserves that asset. -/
theorem physical_transfer_conservation (fromBal toBal amount : Int) :
    (fromBal - amount) + (toBal + amount) = fromBal + toBal := by
  omega

/-- The vault partition resolves to terminal wealth when deltas are zero. -/
theorem terminal_accounting_partition
    (trader₀ trader₁ other₀ other₁ pool₀ pool₁ claim₀ claim₁
      surplus₀ surplus₁ : Int)
    (h : trader₁ + other₁ + pool₁ + claim₁ + surplus₁ =
         trader₀ + other₀ + pool₀ + claim₀ + surplus₀) :
    trader₁ - trader₀ = (other₀ - other₁) + (pool₀ - pool₁)
      + (claim₀ - claim₁) + (surplus₀ - surplus₁) := by
  omega

/-- A lower bound on terminal virtual pool value certifies a bounded trader
    gain after accounting for other accounts, claims, and vault surplus. -/
theorem terminal_extraction_bound
    (gain otherDraw pool₀ pool₁ claimDraw surplusDraw floor : Int)
    (accounted : gain = otherDraw + pool₀ - pool₁ + claimDraw + surplusDraw)
    (floorValid : floor ≤ pool₁) :
    gain ≤ otherDraw + pool₀ - floor + claimDraw + surplusDraw := by
  omega

/-- If a concrete implementation commutes with abstraction on each step,
    an entire call trace commutes with abstraction. This is the remaining
    refinement obligation for any actual EVM interpreter. -/
theorem finite_trace_refinement
    {Concrete Abstract Action : Type}
    (concreteStep : Action → Concrete → Concrete)
    (abstractStep : Action → Abstract → Abstract)
    (encode : Concrete → Abstract)
    (stepCorrect : ∀ action state,
      encode (concreteStep action state) = abstractStep action (encode state))
    (initial : Concrete) (actions : List Action) :
    encode (MathCan.HookState.endpoint concreteStep initial actions) =
      MathCan.HookState.endpoint abstractStep (encode initial) actions := by
  induction actions generalizing initial with
  | nil => rfl
  | cons action rest ih =>
      simp only [MathCan.HookState.endpoint]
      rw [ih (concreteStep action initial)]
      rw [stepCorrect action initial]

#print axioms backed_apply
#print axioms backed_run
#print axioms terminal_vault_solvency
#print axioms mint_claim_neutral
#print axioms clear_neutral
#print axioms revert_restores_backing
#print axioms physical_transfer_conservation
#print axioms claim_transfer_conservation
#print axioms terminal_accounting_partition
#print axioms terminal_extraction_bound
#print axioms finite_trace_refinement

end MathCan.FlashAccounting

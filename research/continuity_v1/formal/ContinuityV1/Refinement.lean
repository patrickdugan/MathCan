import Init

/-!
# Finite event reducer: independent specification and compiled implementation

This formalizes the finite, positive-support portion of Python core.replay.
Every derivation references earlier evidence and retractions target assertions
in admitted Python traces. Lean evaluates even malformed traces, but the
correspondence to Python is claimed only for validated event logs with an
injective numeric-ID renaming. In particular, no storage hash or authorization
assumption is established by these theorems.
-/

namespace SelfModels.ContinuityV1

inductive FiniteEvent where
  | base (eid : Nat) (claim : String)
  | derived (eid : Nat) (claim : String) (premises : List Nat)
  | revoke (eid : Nat) (target : Nat)
  | note (eid : Nat) (version : String) (annotation : String)
  deriving Repr, DecidableEq

structure EvidenceNode where
  eid : Nat
  claim : String
  premises : List Nat
  isBase : Bool
  deriving Repr, DecidableEq

structure Compiled where
  nodes : List EvidenceNode := []
  revoked : List Nat := []
  annotations : List (Nat × String × String) := []
  deriving Repr, DecidableEq

/-- An operational event-collector, analogous to the event-ingest pass. -/
def collectStep (acc : Compiled) : FiniteEvent → Compiled
  | .base eid claim =>
    { acc with nodes := acc.nodes ++ [{eid := eid, claim := claim,
                                       premises := [], isBase := true}] }
  | .derived eid claim premises =>
    { acc with nodes := acc.nodes ++ [{eid := eid, claim := claim,
                                       premises := premises, isBase := false}] }
  | .revoke _ target => { acc with revoked := acc.revoked ++ [target] }
  | .note eid version annotation =>
    { acc with annotations := acc.annotations ++ [(eid, version, annotation)] }

def collectFrom (acc : Compiled) : List FiniteEvent → Compiled
  | [] => acc
  | event :: rest => collectFrom (collectStep acc event) rest

def compiled (events : List FiniteEvent) : Compiled :=
  collectFrom {} events

/-- An independently recursive specification: collect all evidence nodes. -/
def specificationNodes : List FiniteEvent → List EvidenceNode
  | [] => []
  | (.base eid claim) :: rest =>
    {eid := eid, claim := claim, premises := [], isBase := true} :: specificationNodes rest
  | (.derived eid claim premises) :: rest =>
    {eid := eid, claim := claim, premises := premises, isBase := false} :: specificationNodes rest
  | (.revoke _ _) :: rest => specificationNodes rest
  | (.note _ _ _) :: rest => specificationNodes rest

/-- An independently recursive specification: collect global source retractions. -/
def specificationRevoked : List FiniteEvent → List Nat
  | [] => []
  | (.revoke _ target) :: rest => target :: specificationRevoked rest
  | _ :: rest => specificationRevoked rest

def specificationAnnotations : List FiniteEvent → List (Nat × String × String)
  | [] => []
  | (.note eid version annotation) :: rest =>
    (eid, version, annotation) :: specificationAnnotations rest
  | _ :: rest => specificationAnnotations rest

def specification (events : List FiniteEvent) : Compiled :=
  { nodes := specificationNodes events,
    revoked := specificationRevoked events,
    annotations := specificationAnnotations events }

/-- The fold-based collector equals the recursive specification for all streams. -/
theorem collectFrom_refines (events : List FiniteEvent) :
    ∀ acc : Compiled,
      collectFrom acc events =
        { nodes := acc.nodes ++ specificationNodes events,
          revoked := acc.revoked ++ specificationRevoked events,
          annotations := acc.annotations ++ specificationAnnotations events } := by
  induction events with
  | nil =>
    intro acc
    simp [collectFrom, specificationNodes, specificationRevoked,
      specificationAnnotations]
  | cons event rest ih =>
    intro acc
    cases event <;>
      simp [collectFrom, collectStep, specificationNodes,
        specificationRevoked, specificationAnnotations, ih, List.append_assoc]

/-- Operational compilation refines the separately defined event semantics. -/
theorem compiled_refines_specification (events : List FiniteEvent) :
    compiled events = specification events := by
  simpa [compiled, specification] using (collectFrom_refines events {})

/-- Evaluate the evidence DAG in creation order, after all base retractions.
    This is defined on every stream. Its Python equivalence requires unique IDs,
    earlier evidence premises, and assert-only retraction targets. -/
def evidenceStep (revoked : List Nat) (active : List Nat)
    (node : EvidenceNode) : List Nat :=
  if (if node.isBase then !(revoked.contains node.eid)
      else node.premises.all (fun premise => active.contains premise))
  then active ++ [node.eid]
  else active

def activeIDs (collected : Compiled) : List Nat :=
  collected.nodes.foldl (evidenceStep collected.revoked) []

def activeClaims (collected : Compiled) : List String :=
  (collected.nodes.filter
    (fun node => (activeIDs collected).contains node.eid)).map
    (fun node => node.claim)

/-- The same support propagation on operational and specification event graphs. -/
theorem activeIDs_refine (events : List FiniteEvent) :
    activeIDs (compiled events) = activeIDs (specification events) := by
  rw [compiled_refines_specification]

theorem activeClaims_refine (events : List FiniteEvent) :
    activeClaims (compiled events) = activeClaims (specification events) := by
  rw [compiled_refines_specification]

/-- Compositionality of the collector under sequential event ingestion. -/
theorem collectFrom_append (acc : Compiled) (xs ys : List FiniteEvent) :
    collectFrom acc (xs ++ ys) = collectFrom (collectFrom acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons event tail ih =>
    simpa [collectFrom] using (ih (collectStep acc event))

/-- Versioned model-authored narrative annotations cannot change canonical IDs. -/
theorem append_note_preserves_active (events : List FiniteEvent)
    (eid : Nat) (version annotation : String) :
    activeIDs (compiled (events ++ [.note eid version annotation])) =
      activeIDs (compiled events) := by
  simp [compiled, collectFrom_append, collectFrom, collectStep, activeIDs]

/-- The interpreted text can change without changing the supported claims. -/
theorem append_note_preserves_claims (events : List FiniteEvent)
    (eid : Nat) (version annotation : String) :
    activeClaims (compiled (events ++ [.note eid version annotation])) =
      activeClaims (compiled events) := by
  simp [compiled, collectFrom_append, collectFrom, collectStep,
    activeClaims, activeIDs]

/-- Two derivations of one proposition: withdrawing one independent source
    preserves the proposition through its other support path. -/
example : activeIDs (compiled [
    .base 1 "source", .derived 2 "conclusion" [1],
    .base 3 "source", .derived 4 "conclusion" [3],
    .revoke 5 1]) = [3, 4] := by
  decide

/-- A dependent conclusion is invalidated when its only source is revoked. -/
example : activeIDs (compiled [
    .base 1 "source", .derived 2 "conclusion" [1],
    .revoke 3 1]) = [] := by
  decide

end SelfModels.ContinuityV1

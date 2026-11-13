import Init

/-!
GAT-01: exact four-vertex service connectivity polynomial and
finite repair-budget arithmetic. These small proofs are independent
of the OpenAI #104/#186 asymptotic theorem statements.

A four-vertex graph is represented by the six edge bits of a Nat:
(01),(02),(03),(12),(13),(23). All simple paths have length <=3.
-/

namespace MathCan.GraphAuthorization

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def edge4 (mask u v : Nat) : Bool :=
  if u == v then false else
  let a := min u v
  let b := max u v
  if a == 0 && b == 1 then mask.testBit 0
  else if a == 0 && b == 2 then mask.testBit 1
  else if a == 0 && b == 3 then mask.testBit 2
  else if a == 1 && b == 2 then mask.testBit 3
  else if a == 1 && b == 3 then mask.testBit 4
  else if a == 2 && b == 3 then mask.testBit 5
  else false

def reach4 (mask u v : Nat) : Bool :=
  u == v ||
  edge4 mask u v ||
  (List.range 4).any (fun a => edge4 mask u a && edge4 mask a v) ||
  (List.range 4).any (fun a =>
    (List.range 4).any (fun b =>
      edge4 mask u a && edge4 mask a b && edge4 mask b v))

def connected4 (mask : Nat) : Bool :=
  (List.range 4).all (fun u =>
    (List.range 4).all (fun v => reach4 mask u v))

def edgeCount4 (mask : Nat) : Nat :=
  ((List.range 6).filter fun i => mask.testBit i).length

def connectedCount4 (k : Nat) : Nat :=
  ((List.range 64).filter fun mask =>
    connected4 mask && edgeCount4 mask == k).length

/-- The complete connected-graph enumerator in Bernstein edge-count basis. -/
theorem four_vertex_connected_coefficients :
    (List.range 7).map connectedCount4 = [0,0,0,16,15,6,1] := by
  decide

/-- A k-repair universal-service graph needs at most k+1 components.
This lemma states the exact integer arithmetic part of the
graph-theoretic construction. -/
theorem repair_budget_equiv (components budget : Nat)
    (positive : 1 ≤ components) :
    components - 1 ≤ budget ↔ components ≤ budget + 1 := by
  omega

/-- Adding repair budget never invalidates the component-count gate. -/
theorem repair_budget_mono (components b c : Nat)
    (hbc : b ≤ c)
    (h : components ≤ b + 1) :
    components ≤ c + 1 := by
  omega

#print axioms four_vertex_connected_coefficients
#print axioms repair_budget_equiv
#print axioms repair_budget_mono

end MathCan.GraphAuthorization

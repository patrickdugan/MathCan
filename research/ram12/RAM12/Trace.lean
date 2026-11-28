import Lean

open Lean Elab Tactic Meta

/-!
RAM-12 historical source proof trace probe. This tactic logs the current
compiler-elaborated proof goals before an existing certified tactic. It does
not synthesize goals, change the proof, or admit any declaration.
-/

elab "ram12_observe" tag:str : tactic => do
  pruneSolvedGoals
  let goals ← getGoals
  let mut printed : Array String := #[]
  let mut names : Array Name := #[]
  for goal in goals do
    printed := printed.push (← ppGoal goal).pretty
    let declaration ← goal.getDecl
    names := names ++ declaration.type.getUsedConstants
    for localDecl in declaration.lctx do
      names := names ++ localDecl.type.getUsedConstants
  let env ← getEnv
  let mut defs : Array String := #[]
  for name in names do
    if name.toString.startsWith "MathCan." then
      if let some (.defnInfo _) := env.find? name then
        if !defs.contains name.toString then
          defs := defs.push name.toString
  let value := Json.mkObj [
    ("id", toJson tag.getString),
    ("goals", toJson printed),
    ("definitions", toJson defs)
  ]
  logInfo m!"RAM12_STATE_JSON:{value.compress}"

import Lean
import MathCan.Hodge
import MathCan.QuantizedJet

open Lean Elab Command

private def nameParts : Name → List Json
  | .anonymous => []
  | .str p s => nameParts p ++ [Json.arr #[toJson "str", toJson s]]
  | .num p n => nameParts p ++ [Json.arr #[toJson "num", toJson n]]

private def kindLabel : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient_primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def dependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut refs := ci.type.getUsedConstants
  if let some value := ci.value? true then
    refs := refs ++ value.getUsedConstants
  match ci with
  | .inductInfo v => refs := refs ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => refs := refs.push v.induct
  | .recInfo v =>
      refs := refs ++ v.all.toArray
      for rule in v.rules do
        refs := (refs.push rule.ctor) ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return refs

elab "audit_native_roots" : command => do
  let env ← getEnv
  let roots := #[`MathCan.Hodge.closed_path_gauge,
    `MathCan.QuantizedJet.nearest_residual,
    `MathCan.QuantizedJet.corrected_error_identity,
    `MathCan.QuantizedJet.corrected_step_stable,
    `MathCan.QuantizedJet.correction_alphabet_bound,
    `MathCan.QuantizedJet.corrected_stream_stable,
    `MathCan.QuantizedJet.vector_predictor_stable]
  let mut todo := roots.toList
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "missing constant {n}"
    let refs := dependencies ci
    todo := refs.toList ++ todo
    rows := rows.push <| Json.mkObj [
      ("name",toJson n.toString),
      ("name_components",Json.arr (nameParts n).toArray),
      ("kind",toJson (kindLabel ci)),
      ("dependencies",Json.arr (refs.map (fun r => toJson r.toString))),
      ("dependency_components",Json.arr (refs.map (fun r => Json.arr (nameParts r).toArray)))]
  let report := Json.mkObj [
    ("scope",toJson "Lean 4.35.0 native environment graph; not pinned NDJSON export"),
    ("roots",toJson (roots.map Name.toString)),
    ("records",Json.arr rows)]
  liftIO <| IO.FS.writeFile "../native_dependency_graph.json" (report.pretty ++ "\n")
  logInfo m!"Native graph: {rows.size} constants"

audit_native_roots

#check MathCan.Hodge.closed_path_gauge
#check MathCan.QuantizedJet.corrected_stream_stable

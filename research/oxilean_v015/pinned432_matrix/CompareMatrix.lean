import Lean
import Export.Parse
import ApproximationMathlib.WordTransport

open Lean Elab Command

-- Independent comparison normalization: erase mdata and the non-semantic
-- let nondep optimization hint; preserve binders, constants, levels and terms.
private partial def norm (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some r := (← get)[e]? then return r
  let r ← match e with
    | .mdata _ b => norm b
    | .app f a => return e.updateApp! (← norm f) (← norm a)
    | .lam _ d b _ => return e.updateLambdaE! (← norm d) (← norm b)
    | .forallE _ d b _ => return e.updateForallE! (← norm d) (← norm b)
    | .letE _ d v b _ => return e.updateLet! (← norm d) (← norm v) (← norm b) false
    | .proj _ _ b => return e.updateProj! (← norm b)
    | _ => pure e
  modify (·.insert e r)
  return r

private def normalized (e : Expr) : Expr := (norm e).run' {}

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

elab "compare_export_to_source" : command => do
  let some out ← liftIO <| IO.getEnv "REPLAY_OUT" | throwError "REPLAY_OUT missing"
  let native ← getEnv
  let parsed ← liftIO <| IO.FS.withFile (out ++ "/Lemmas.ndjson") .read fun h =>
    Export.parseStream (IO.FS.Stream.ofHandle h)
  let mut rows : Array Json := #[]
  for name in parsed.constOrder do
    let some a := native.find? name | throwError "not in native source environment: {name}"
    let some b := parsed.constMap[name]? | throwError "parsed declaration absent: {name}"
    unless a.name == b.name && a.levelParams == b.levelParams && kind a == kind b do
      throwError "name/universe/kind mismatch: {name}"
    unless normalized a.type == normalized b.type do
      throwError "statement mismatch: {name}"
    match a.value? true, b.value? true with
    | some av, some bv =>
        unless normalized av == normalized bv do throwError "proof/value mismatch: {name}"
    | none, none => pure ()
    | _, _ => throwError "proof/value presence mismatch: {name}"
    rows := rows.push <| Json.mkObj [("name",toJson name.toString),
      ("kind",toJson (kind a)), ("type_equal",toJson true),
      ("value_equal_after_metadata_normalization",toJson true),
      ("level_parameters_equal",toJson true)]
  unless parsed.constMap.contains `MathCan.WordCapture.decoded_approximation do
    throwError "intended target is absent"
  let report := Json.mkObj [("status",toJson "matched"),
    ("normalization",toJson "mdata erased; let nondep set false; no reduction or axiom substitution"),
    ("constants_compared",toJson rows.size), ("records",Json.arr rows)]
  liftIO <| IO.FS.writeFile (out ++ "/source_export_comparison.json") (report.pretty ++ "\n")
  logInfo m!"Compared {rows.size} exported constants with unchanged source: all types and values match"

compare_export_to_source
#check MathCan.WordCapture.decoded_approximation
#print axioms MathCan.WordCapture.decoded_approximation

#print axioms MathCan.WordTransport.directional_append
#print axioms MathCan.WordTransport.basis_cons
#print axioms MathCan.WordTransport.directional_component
#print axioms MathCan.WordTransport.directional_contDiff
#print axioms MathCan.WordTransport.directional_ofFn
#print axioms MathCan.WordTransport.repeated_component
#print axioms MathCan.WordTransport.tensor_scale
#print axioms MathCan.WordTransport.factorial_transport
#print axioms MathCan.WordTransport.row_compatibility
#print axioms MathCan.WordTransport.size_formula
#print axioms MathCan.WordTransport.word_length
#print axioms MathCan.WordTransport.word_pack
#print axioms MathCan.WordTransport.matrix_integral
#print axioms MathCan.WordTransport.matrix_application
#print axioms MathCan.WordTransport.matrix_compatibility
#print axioms MathCan.WordTransport.row_sub
#print axioms MathCan.WordTransport.row_bound
#print axioms MathCan.WordTransport.step_norm
#print axioms MathCan.WordTransport.matrix_residual
#print axioms MathCan.WordTransport.value_label
#print axioms MathCan.WordTransport.values_bound
#print axioms MathCan.WordTransport.evaluation_error
#print axioms MathCan.WordTransport.evaluation_values
#print axioms MathCan.WordCapture.finite_parameters
#print axioms MathCan.WordCapture.amount_bound
#print axioms MathCan.WordCapture.predict_bound
#print axioms MathCan.WordCapture.innovation
#print axioms MathCan.WordCapture.packet_update
#print axioms MathCan.WordCapture.frames_length
#print axioms MathCan.WordCapture.reference_accuracy
#print axioms MathCan.WordCapture.captured_accuracy
#print axioms MathCan.WordCapture.targets_residuals
#print axioms MathCan.WordCapture.normalized_approximation
#print axioms MathCan.WordCapture.decoded_approximation

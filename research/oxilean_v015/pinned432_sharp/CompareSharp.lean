import Lean
import Export.Parse
import ApproximationMathlib.SharpTransport

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
  unless parsed.constMap.contains `MathCan.HolderCapture.holder_decoded_approximation do
    throwError "intended target is absent"
  let report := Json.mkObj [("status",toJson "matched"),
    ("normalization",toJson "mdata erased; let nondep set false; no reduction or axiom substitution"),
    ("constants_compared",toJson rows.size), ("records",Json.arr rows)]
  liftIO <| IO.FS.writeFile (out ++ "/source_export_comparison.json") (report.pretty ++ "\n")
  logInfo m!"Compared {rows.size} exported constants with unchanged source: all types and values match"

compare_export_to_source
#check MathCan.HolderCapture.holder_decoded_approximation
#print axioms MathCan.HolderCapture.holder_decoded_approximation

#print axioms MathCan.SharpResidual.component_contDiff
#print axioms MathCan.SharpResidual.scaled_tensor_residual
#print axioms MathCan.SharpResidual.normalized_tensor_residual
#print axioms MathCan.SharpResidual.top_component_residual
#print axioms MathCan.SharpJet.isometry_derivative_difference
#print axioms MathCan.SharpJet.fderiv_derivative_difference
#print axioms MathCan.SharpJet.iterated_derivative_difference
#print axioms MathCan.SharpJet.component_derivative_difference
#print axioms MathCan.SharpJet.sharp_component_transport
#print axioms MathCan.SharpJet.uniform_component_budget
#print axioms MathCan.SharpJet.sharp_jet_transport
#print axioms MathCan.SharpAlphabet.prediction_error
#print axioms MathCan.SharpAlphabet.innovation_bound
#print axioms MathCan.SharpAlphabet.sharp_frame
#print axioms MathCan.SharpAlphabet.analytic_sharp_frame
#print axioms MathCan.SharpAlphabet.component_sharp_frame
#print axioms MathCan.SharpAlphabet.sharp_frames
#print axioms MathCan.SharpAlphabet.sharp_decoded_accuracy
#print axioms MathCan.SharpCapture.jet_accuracy
#print axioms MathCan.SharpCapture.smooth_decoded_approximation
#print axioms MathCan.SharpCapture.holder_decoded_approximation
#print axioms MathCan.HolderCapture.constant_prediction
#print axioms MathCan.HolderCapture.holder_step_residual
#print axioms MathCan.HolderCapture.holder_residuals
#print axioms MathCan.HolderCapture.holder_decoded_approximation

import Lean
import Export.Parse
import ApproximationMathlib.CubeApproximation

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
  unless parsed.constMap.contains `MathCan.CubeSpatial.approximation do
    throwError "intended target is absent"
  let report := Json.mkObj [("status",toJson "matched"),
    ("normalization",toJson "mdata erased; let nondep set false; no reduction or axiom substitution"),
    ("constants_compared",toJson rows.size), ("records",Json.arr rows)]
  liftIO <| IO.FS.writeFile (out ++ "/source_export_comparison.json") (report.pretty ++ "\n")
  logInfo m!"Compared {rows.size} exported constants with unchanged source: all types and values match"

compare_export_to_source
#check MathCan.CubeSpatial.approximation
#print axioms MathCan.CubeSpatial.approximation

#print axioms MathCan.CubeTaylor.cube_convex
#print axioms MathCan.CubeTaylor.cube_uniqueDiff
#print axioms MathCan.CubeTaylor.cube_segment
#print axioms MathCan.CubeTaylor.dir_smooth
#print axioms MathCan.CubeTaylor.dir_tensor
#print axioms MathCan.CubeTaylor.line_smooth
#print axioms MathCan.CubeTaylor.line_derivatives
#print axioms MathCan.CubeTaylor.dir_ofFn
#print axioms MathCan.CubeTaylor.line_polynomial
#print axioms MathCan.CubeTaylor.line_tensor
#print axioms MathCan.CubeTaylor.holder_remainder
#print axioms MathCan.CubeTaylor.value_label
#print axioms MathCan.CubeTaylor.evaluation_values
#print axioms MathCan.CubeTaylor.axes_tensor
#print axioms MathCan.CubeTaylor.axes_difference
#print axioms MathCan.CubeTaylor.values_axes
#print axioms MathCan.CubeTaylor.row_compatibility
#print axioms MathCan.CubeTaylor.row_zero
#print axioms MathCan.CubeTaylor.axis_line_polynomial
#print axioms MathCan.CubeTaylor.axis_line_holder
#print axioms MathCan.CubeTaylor.axis_remainder
#print axioms MathCan.CubeTaylor.values_bound
#print axioms MathCan.CubeTaylor.matrix_residual
#print axioms MathCan.CubeTaylor.evaluation_error
#print axioms MathCan.CubeAnchors.digit_div
#print axioms MathCan.CubeAnchors.digit_mod
#print axioms MathCan.CubeAnchors.unrank_bound
#print axioms MathCan.CubeAnchors.unrank_rank
#print axioms MathCan.CubeAnchors.anchor_in_cube
#print axioms MathCan.CubeAnchors.clip_rescale
#print axioms MathCan.CubeAnchors.safe_coverage
#print axioms MathCan.CubeAnchors.selected_anchor
#print axioms MathCan.CubeAnchors.selected_coverage
#print axioms MathCan.CubeCapture.axis_segment
#print axioms MathCan.CubeCapture.targets_residuals
#print axioms MathCan.CubeCapture.normalized_approximation
#print axioms MathCan.CubeCapture.decoded_approximation
#print axioms MathCan.CubeWalk.adjacent_symm
#print axioms MathCan.CubeWalk.adjacent_cons
#print axioms MathCan.CubeWalk.adjacent_head
#print axioms MathCan.CubeWalk.unrank_step
#print axioms MathCan.CubeWalk.point_in_cube
#print axioms MathCan.CubeWalk.lattice_step
#print axioms MathCan.CubeWalk.delta_motion
#print axioms MathCan.CubeWalk.adjacent_motion
#print axioms MathCan.CubeWalk.clamp_cast
#print axioms MathCan.CubeWalk.point_anchor
#print axioms MathCan.CubeWalk.edge_step
#print axioms MathCan.CubeWalk.schedule_length
#print axioms MathCan.CubeWalk.anchors_zero
#print axioms MathCan.CubeWalk.anchors_succ
#print axioms MathCan.CubeWalk.schedule_anchors
#print axioms MathCan.CubeSpatial.query_fine
#print axioms MathCan.CubeSpatial.query_valid
#print axioms MathCan.CubeSpatial.schedule_inside
#print axioms MathCan.CubeSpatial.schedule_selected
#print axioms MathCan.CubeSpatial.micro_scale_le_one
#print axioms MathCan.CubeSpatial.approximation

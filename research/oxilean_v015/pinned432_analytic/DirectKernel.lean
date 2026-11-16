import LeanChecker

/-! Native kernel replay through the unmodified pinned LeanChecker API.
This omits only the stock CLI's recursive scan of every olean search path. -/
open Lean
unsafe def runAnalyticKernelChecks : IO Unit := do
  initSearchPath (← findSysroot)
  for m in #[`ApproximationMathlib.TaylorFoundation, `ApproximationMathlib.SmoothTaylor,
      `ApproximationMathlib.CapturedApproximation] do
    IO.println s!"Checking {m} with pinned LeanChecker.replayFromImports"
    replayFromImports m
    IO.println s!"Accepted {m}"
#eval runAnalyticKernelChecks

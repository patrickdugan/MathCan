import LeanChecker
open Lean
unsafe def runSynthesisKernelChecks : IO Unit := do
  initSearchPath (← findSysroot)
  for m in #[`ApproximationMathlib.JetSynthesis, `ApproximationMathlib.FrameSynthesis, `ApproximationMathlib.MultivariateTaylor, `ApproximationMathlib.MultivariateBounds, `ApproximationMathlib.MultivariateHolder, `ApproximationMathlib.SynthesisCapture, `ApproximationMathlib.MultivariateCapture] do
    IO.println s!"Checking {m} using pinned replayFromImports"
    replayFromImports m
    IO.println s!"Accepted {m}"
#eval runSynthesisKernelChecks

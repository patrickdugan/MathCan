import LeanChecker
open Lean
unsafe def runSharpKernelChecks : IO Unit := do
  initSearchPath (← findSysroot)
  for m in #[`ApproximationMathlib.SharpTransport] do
    IO.println s!"Checking {m} using pinned replayFromImports"
    replayFromImports m
    IO.println s!"Accepted {m}"
#eval runSharpKernelChecks

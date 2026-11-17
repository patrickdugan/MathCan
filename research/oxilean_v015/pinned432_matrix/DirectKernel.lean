import LeanChecker
open Lean
unsafe def runMatrixKernelChecks : IO Unit := do
  initSearchPath (← findSysroot)
  IO.println "Checking ApproximationMathlib.WordTransport using pinned replayFromImports"
  replayFromImports `ApproximationMathlib.WordTransport
  IO.println "Accepted ApproximationMathlib.WordTransport"
#eval runMatrixKernelChecks

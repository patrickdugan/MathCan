import LeanChecker
open Lean
unsafe def runCubeKernelChecks : IO Unit := do
  initSearchPath (← findSysroot)
  IO.println "Checking ApproximationMathlib.CubeApproximation using pinned replayFromImports"
  replayFromImports `ApproximationMathlib.CubeApproximation
  IO.println "Accepted ApproximationMathlib.CubeApproximation"
#eval runCubeKernelChecks

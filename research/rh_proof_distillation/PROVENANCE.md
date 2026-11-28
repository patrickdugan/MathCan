# MathCan RH source ledger

Upstream: leanprover-community/riemann-hypothesis
pinned commit f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3.
Prior experimental home: MoralityLabAI/EvalMath PR #60.

All files in this directory labeled as compiled references were
derived from the original published Lean cache and SHA-pinned
in the EvalMath CI receipts. The source notes were moved from
the EvalMath research branch at its 2026-11-21 version.

The exact numerical scalar oracles are executable in MathCan.
MathCan's separate native Lean file proves integer arithmetic
certificates without the original Mathlib dependency.
Full source-level RH proof bodies remain in the original
leanprover-community repository; no such bodies are vendored here.

Core source files:
- src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean
- src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean
- src/Formalism/SharpRestriction/GlobalSchurBounds/ZetaZeroFreeRegion.lean
- src/Formalism/SharpRestriction/GlobalSchurBounds/RamificationTwoAndConjugationAtQAndD.lean
- src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean
- src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean

# FPB-01: Fourier-blind Boolean modes, Lean bridge

Companion to [Compactification Theory FPB-01 PR #120](https://github.com/MoralityLabAI/Compactification-Theory/pull/120).

The new mathematical campaign pairs OpenAI Math #132 (sensitivity/block-sensitivity separation) and #192 (unbounded singleton Fourier sum relative to square-root Fourier degree), developing a selector-controlled function with a hidden Fourier-blind coordinated mode.

MathCan/FourierBlockProbe.lean checks the **one-bit Fourier transport basis case** under the pinned Lean 4 Init library:

- A simultaneous flip of the x and y registers leaves f(x XOR y) unchanged.
- If a hidden bit is sensitive, independently flipping either observed register is sensitive.
- Both singleton signed Fourier numerators of the two-input XOR lift are exactly zero.
- The paired Fourier numerator is 2(a-b), hence its normalized two-bit coefficient equals the original one-bit source coefficient (a-b)/2.

The general n-bit transport identity follows by tensorized character orthogonality and is written in the Compactification Theory theorem note. The 17-bit Rubinstein/sentinel example, finite selector, heldout synthetic probe data and 34-dimensional numerical checks are handled by exact Python. The original OpenAI #132/#192 mathematical claims are conditional source results and are NOT formalized by this small Lean bridge.

The source code includes transitive axiom printing; the MathCan proof-audit workflow rejects admitted sorries and native reduction shortcuts. The branch is intended for review and keeps previous FHC, DMB and GAT Lean imports intact.

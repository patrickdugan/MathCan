# FHC-01: finite-horizon kernel bridge

Companion: [Compactification Theory FHC-01 PR #111](https://github.com/MoralityLabAI/Compactification-Theory/pull/111).

The source combination uses OpenAI Math #094, finite-set dimension reduction
in Lp, and #098, compact doubling Hilbert sets without any fixed
finite-dimensional bi-Lipschitz embedding.

This MathCan branch formalizes two **elementary** subsidiary claims:

- The exact discrete one-sixth threshold: 6 epsilon <= delta is
  equivalent to delta+2 epsilon <= 2(delta-2 epsilon).
  It is the alpha=2, D=1 cross-multiplied robust-net transfer step.
- If observing the first T entries covers the entire finite state word,
  matching observations imply the words are equal.

The implementation lives in MathCan/FiniteHorizonGap.lean, with Lean
kernel compilation and transitive-axiom printing in the existing
mathcan-proof-audit GitHub workflow. It uses only the pinned Init
library. The full compactness lemma, Gaussian Hilbert-to-L4 isometry,
OpenAI source results, and quantitative source distortion estimates
remain handwritten proofs, as clearly marked in the FHC-01 theory note.

This proof is deliberately scoped to operations we can independently
kernel-check; it is not a formalization of all OpenAI Math #094/#098.

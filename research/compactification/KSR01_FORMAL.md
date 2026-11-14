# KSR-01: finite tree-reconstruction kernel bridge

Companion to [Compactification Theory KSR-01 PR #124](https://github.com/MoralityLabAI/Compactification-Theory/pull/124).

The source pair is OpenAI Mathematics #229, three-state symmetric
broadcast reconstruction thresholds, and #236, factor-of-IID
threshold for free zero-field Ising spins on infinite regular trees.

This MathCan bridge is limited to exact finite arithmetic in
MathCan/TreeReconstruction.lean. It checks:

- The q=3 symmetric Markov channel with diagonal numerator 13,
  off-diagonal 1 and row denominator 15; the centered 3-state
  contrast has eigenvalue 12/15=4/5.
- At b=2 and lambda=4/5, the normalized second-moment numerator
  A_0=1, A_(L+1)=25*A_L +16*32^L.
- The exact gap identity 7*A_L+9*25^L=16*32^L, which implies
  V_L=A_L/32^L<=16/7.
- The independent half-retention moment correction:
  7*(A_L+25^L)+2*25^L=16*32^L.
- The critical b=4, lambda=1/2 variance numerator 4+3L.

The probability-theoretic step from bounded leaf-score
variance to Bayes root accuracy is proved in the companion
theory note and tested by exact rational finite posterior
enumeration. This small Lean file does not formalize the
original source #229 q=3 full threshold or #236 infinite
factor-of-IID construction, nor provide an Ising finitary
coding radius.

Kernel compilation and transitive axiom printing use the
existing pinned MathCan Lean 4 workflow. Native reduction
shortcuts and admitted axioms are prohibited in that workflow.

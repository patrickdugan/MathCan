# GAL-04: online compactification and safety capital

Full derivations and experiments:
https://github.com/MoralityLabAI/Compactification-Theory/blob/research/gal01-nonperturbative-20261128/Galacticity/GAL04.md

MathCan/GalacticityMarkets.lean contains ten core-Lean arithmetic
certificates: rent optimality, threshold purchase upper bounds,
prediction consistency, independent epoch addition, prefix fallback,
prefix admission, rejection reserves, and first-acquisition
zero/positive premium obstructions. The full online sequence
argument, classical deterministic lower bound, general prediction
robustness and dynamic programming correctness are paper proofs.
The standalone CI workflow checks the new module. The cost
guarantee is relative to direct execution under a known exact
cost ledger, not to offline optimum or physical wall time.

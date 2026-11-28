# GAL-03: rank discovery and observation cost

Full derivations, experiments and BPD connection:
https://github.com/MoralityLabAI/Compactification-Theory/blob/research/gal01-nonperturbative-20261128/Galacticity/GAL03.md

MathCan/GalacticityAccess.lean uses core Lean to generalize the finite
adaptive query tree to arbitrary output, show that an unread spike has
the all-zero transcript, force every coordinate onto an exact zero
verifier's path, and show that two missing coordinates cannot both be
possible when the spike location must be output. These are finite-tree
semantic lemmas, not formalized matrix-rank or cardinality theorems.
For Q = Fin n × Fin p, counting the coordinates gives the np exact
zero-input bound and the np-1 single-spike discovery bound on paper.
It also contains two elementary amortization inequalities.

The two-sided randomized lower bound follows on paper by coupling
the random seeds on zero and on a spike at j: the probability of
probing j on the zero path must be >=1-2e. Sum over all coordinates.
The full probabilistic argument, rank-one representation cardinality,
fixed-basis conditioning, and repeated-column worst-case formula
remain mathematical derivations outside the kernel. The experiments
are exact synthetic operation counts, not wall-clock or neural evidence.

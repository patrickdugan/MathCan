# NOR-32: finite unknown-support coverage duality

Companion to [Compactification-Theory NOR-32](https://github.com/MoralityLabAI/Compactification-Theory/pull/201), registered before any new NOR-32 output data (first commit 07f0f912).

The original NOR-23 exact combinatorics counted the number of size-k AUDIT sets that miss an independently fixed radius-r changed output. NOR-32 examines the **dual** threat experiment: the audit chooses a fixed size-k inspection set, while the attacker draws an independent uniform radius-r alteration subset of a specified, potentially unfamiliar s-position support.

Represent the s possible attack positions as an indexed list with True exactly where the fixed audit also inspects those support positions. Let t be the number of true entries. The number of possible r-subset attacks is C(s,r). The number avoiding every inspected support coordinate is exactly C(s-t,r). Therefore the conditional uniform-within-support detection probability is

\[
P(\mathrm{detect}\mid\mathrm{OOD\ support}\ S,\mathrm{fixed\ audit}\ T)
=1-\frac{\binom{|S\setminus T|}{r}}{\binom{|S|}{r}}.
\]

The module MathCan/NOR32UnknownSupportCoverage.lean proves this exact count and conditional fraction from NOR-23's standalone Lean combinatorial enumerator. Crucially, if the unknown support equals the whole m-coordinate future, *every* fixed k-coordinate audit has the **same** uniform radius-r attack miss/total pair C(m-k,r) and C(m,r). A theorem proves this pair equality for any two k-budget audits. Another proves that every arm in an arbitrary finite mixture has that same baseline pair under the uniform blind-attack distribution.

The uniform audit has the same success probability when it randomizes inspection positions against a fixed r-attack:

\[
1-\frac{\binom{m-r}{k}}{\binom{m}{k}}
=1-\frac{\binom{m-k}{r}}{\binom{m}{r}}.
\]

This equality follows by counting disjoint audit/attack subset pairs from either side. Under a uniform blind-attack adversary, an equally budgeted nonuniform audit mixture cannot improve the **average across all attack sets**. Improvements on particular procedural supports therefore change the source-conditioned coverage distribution. This is the no-free-lunch boundary for the forthcoming six-support transfer test, and it is compatible with all earlier NOR-25 to NOR-31 conditional source-family gains.

A separately proved counterexample constructs a changed future whose exact-value witness transcript is identical after the attacker sees the **complete realized audit set** and changes an unchecked coefficient. The detection bounds require attacks fixed before independently sampled random coins and an authentic external exact target coefficient witness; public deterministic experiment PRNG seeds are reproducibility tools rather than cryptographic secrets.

The applied experiment includes six prospective **new procedural support generators** central96, stride17_96, low_abs96, curvature96, anti_prior96, and hash96, with 24 fresh public-only source identities and equal-budget comparisons of the frozen NOR-31 mixture, hybrid_50 and uniform16. The original support-generator families are absent from historical policy fitting. Kernel mathematics proves finite counts, rather than empirical generalization or source-model soundness.

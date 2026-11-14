# SCT-01: SAT core threshold and streaming-monitor formalization

Companion to the Compactification Theory research campaign at
research/refutation_bench/sct01_threshold_witness/.

Selected public sources:
- OpenAI Mathematics #175, Talagrand integral and fractional expectation threshold comparison.
- OpenAI Mathematics #235, limiting random k-SAT thresholds and first UNSAT hitting-time distributions.

Both are external source results. The companion research derives exact finite
theorems for a *restricted* two-gadget uniform 3-SAT clause universe.

## Kernel scope

MathCan/SATCoreThreshold.lean verifies the semantics of a complete
three-variable 3-SAT gadget in which each of eight signed proper clauses
excludes one of the eight local assignments. For all 256 clause subsets,
the complete eight-clause gadget is the unique UNSAT member. Its
eight immediate seven-clause subformulas are SAT.

For two gadgets on disjoint variable triples, the kernel checks the
factorized SAT predicate: both local blocks must remain incomplete.
The independent Python SAT oracle enumerates all 65,536 clause subsets
and all 64 possible six-variable assignments.

The file also certifies finite arithmetic for the minimal deterministic
streaming monitor states: 65026 states for exact SAT decision and 65027
for exact SAT-or-valid-core-index output, both requiring 16 fixed bits.
It kernel-checks injectivity of a base-255 two-digit encoding of incomplete
clause masks. A general Myhill–Nerode lower-bound proof and an explicit
matching automaton are supplied in the companion THEORY.md, with separate
exhaustive finite tests.

The finite proof verifies that identifying one of eight uniquely completed
gadget indices requires three fixed bits, given a static public decoder
table and a promise that precisely one gadget has been completed.

## Limits

The mathematical derivation of exact expectation cover cost
min(1,r p^8), its fractional-cover optimum, and exact hitting-time
moments relies on elementary finite combinatorics proved in the companion
theory note and independently checked via Python Fractions.
Those probability and cover theorems are **not** fully Lean formalized here.

The larger source #175 universal comparison constant and #235 large-n
random SAT threshold/variance assertions are outside the small Lean
module. The six-variable clause distribution restricts to two disjoint
variable triples; it differs from the source full uniform six-variable
random 3-SAT model. No native Lean reasoner or language-model checkpoint
has been evaluated.

CI builds the pinned MathCan library, checks all transitive axioms and
runs its existing rational regression suite.

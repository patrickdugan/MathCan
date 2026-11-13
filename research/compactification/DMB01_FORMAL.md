# DMB-01: deletion memory barrier, Lean bridge

Research companion to [Compactification Theory PR #112](https://github.com/MoralityLabAI/Compactification-Theory/pull/112).

OpenAI Math #122 addresses worst-case deletion trace reconstruction. OpenAI Math #140 addresses Gaussian streaming memory/precision. The primary theory note combines their constraints with new finite-state cardinality, data-processing, deletion-deck and angular-cap arguments.

This MathCan file checks *finite discrete* pieces in Lean 4 / Init:

- A correct deterministic terminal decoder must assign distinct states to two distinct source words.
- All seven possible deletion traces of length <=2 have identical counts for 0110 and 1001, with positions 0..3 counted by deletion masks.
- All eight length-three trace supports of those two words are disjoint.
- Each source has four length-three deletion-mask paths and one fully retained trace.

The source channel probability at deletion q=4/5 is computed independently in exact Fraction Python. The probability theorem TV=17/625 and m-fold Le Cam bounds are paper proofs with finite rational checks, not Lean theorems here.

The new Lean lemmas use ordinary decide reduction, without sorry or native_decide. CI builds MathCan and prints all transitive axioms.

This file deliberately does not claim that the original asymptotic OpenAI math theorems have been kernel-verified by this project.

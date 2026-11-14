# TFH-01 | Structural-zero matching fibres

Two OpenAI math inspirations:

- Result #113: *Entropy and Face Dimension of the Perfect Matching Polytope*, https://github.com/openai/math/blob/main/preprints/Entropy-and-Face-Dimension-of-the-Perfect-Matching-Polytope-September-23-2026/main.pdf
- Result #115: *An FPRAS for Cell-Bounded Contingency Tables*, https://github.com/openai/math/blob/main/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/main.pdf

## Independent results

A finite incidence matrix with forbidden cells defines a fibre of
quota-constrained assignments. Our 3x3 six-cycle contains exactly two legal
matchings and **no legal 2x2 switch** from either. A Markov sampler restricted
to pair switches is reducible. The full-fibre uniform distribution requires
a larger alternating-cycle move or global continuation counting. When a
pair-switch chain starts at one matching, it loses ln(2) nats of entropy
relative to the uniform target on the two matchings.

For any family quota vector q with sum q = n, the exact Hall-cut deficit is

    delta = max_{S subset families} (sum_{j in S} q[j] - |N(S)|)_+.

Expanding family j into q[j] identical slots and applying the standard
maximum-matching deficiency theorem yields maximum filled slots n-delta.
If p is a one-pass distinct-state action distribution and u the target
quota distribution, the same cut forces TV(p,u) >= delta/n. The original
proof and Python implementation are in the companion LoopedTransformers
TFH-01 campaign.

## Application to the frozen FC-12 training evidence

FC-12 observed 51 original train Lean goal states, with one progressing
compiler *attempt* each for exact_local and rcases_local. Each family thus
has at most one eligible distinct training state; their union has at most
two. Hypothetical 13-slot quotas for both demand 26 slots. Therefore the
combined Hall shortage is at least 24, and the one-pass action distribution
has TV at least 24/51 from the proposed balanced target. Repeated examples
are outside the distinct-state coverage statement. An exact assignment
needs the full compiler-positive incidence matrix.

## Proof boundary

MathCan/TacticFibers.lean checks the exact 3x3 schedule classification,
both legality witnesses, both 2x2 obstruction lemmas, and the Nat shortfall
and scaled-TV lemmas. It imports no manuscript-level axioms and contains no
sorry. The general finite max-flow/Hall argument and the variational TV
argument above have their paper proofs here; a generic formal Lean
encoding is a separate task. The Python test enumerates all 512 3x3
structural-zero masks.

    lake build MathCan
    lake env lean MathCan/TacticFibers.lean
    python -m unittest discover -s tests -p 'test_tactic_fibers.py' -v

This is prospective TFH-01 mathematical work; FC-12/13 protocols and
registered evaluation scores remain frozen.

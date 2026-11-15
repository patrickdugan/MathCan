# PEF-07 | Context-closed causal-history generalization

This document is the formal mathematical companion to the PEF-07
twelve-bit prospective benchmark in
[LoopedTransformers PR #67](https://github.com/MoralityLabAI/LoopedTransformers/pull/67).

The prior PEF-03 to PEF-06 campaigns repeatedly examined a finite
eight-bit input family. PEF-07 introduces a new twelve-bit family
with four focal oldest bits and eight independent context bits.
All 256 context assignments are partitioned into 160/48/48
disjoint groups for trunk training, probe fitting and heldout
evaluation. Every group contains all sixteen combinations of
the four focal bits. This prevents individual or paired old-bit
counterfactuals from crossing the source partitions.

## Two exact Boolean teachers

Write the four focal bits as a,b,c,d. Define

    C(a,b,c,d) = (a AND b) XOR (c AND d)
    T(a,b,c,d) = indicator(a+b+c+d >= 2).

For a complete four-bit input cube, exactly 6 of 16 C targets
are one, and 11 of 16 T targets are one. A decoder depending
only on the context has the same output for all sixteen old-bit
assignments. Its maximum number of correct predictions on one
complete group is therefore 10 for C and 11 for T.

For an arbitrary finite list of K complete context groups,
even if the source contexts contain repetitions, any
context-only Boolean predictor has at most

    10 K correct C predictions out of 16 K
    11 K correct T predictions out of 16 K.

For 48 heldout contexts, these bounds are exactly **480/768**
and **528/768**, giving a deterministic source-only Bayes
ceiling of **62.5%** and **68.75%**. Every outcome above this
ceiling must depend on some information about the four focal
old bits, provided the source grouping and predictions are
as specified. This does not prove which hidden circuit
stores that information.

## Two kinds of paired-bit interaction

At focal input 0000, all four individual bit flips leave both
teacher labels unchanged. The coalition C changes from zero
to one for exactly two of the six double-bit flips:
the complete paired gates (0,1) and (2,3).
The four cross-pairs remain inactive.

The threshold T changes from zero to one for all six
double-bit flips. Its *prethreshold score* a+b+c+d-1.5 is
a separable additive function with zero four-corner
mixed difference. Thus an observed pair-only *class*
change by itself does not establish mixed continuous-logit
interactions. The exact neural experiment separately
compares four-corner logit differences and an additive
surrogate made from actual singleton responses.

## Formal Lean scope

MathCan/CoalitionContextBound.lean proves:
- exact 16-input teacher label counts 6 and 11;
- generic arbitrary-context predictor bounds 10/16 and 11/16;
- the accumulated upper bounds for *any finite list* of contexts;
- four singleton-inactive and the intended/cross-pair teacher
  intervention truth values;
- zero mixed teacher additive-score identities;
- numerical ceilings for 48 full context blocks.

The finite teacher formulas and the generic list inequality
are kernel-checked with no admitted theorem. These are
source-design and information-counting certificates. They
do not formalize the neural training procedure or predict
which optimizer seed will learn either task.

The local PEF-07 CPU experiment trained six 32D tied-attention
recurrent models and reported perfect 768/768 native h12
and newly fitted h14 head accuracy on both tasks across
all seeds, with an independent frozen-checkpoint replay.
The GitHub-hosted experiment remains unverified because
the job failed before runner steps. The local evidence is
labeled accordingly in the empirical repository.

The next prospective generalization campaign should hold
out a novel Boolean operator composition or change
the interacting bit positions, since PEF-07 itself
holds out distractor contexts while preserving teacher
logic across train and test.

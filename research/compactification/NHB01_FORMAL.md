# NHB-01: finite noisy-horizon kernel bridge

Date: 2026-11-14. Companion to [Compactification Theory PR #129](https://github.com/MoralityLabAI/Compactification-Theory/pull/129).

The source pair is OpenAI Math #119 (sharp binary-information contraction) and #127 (average sensitivity of polynomial threshold functions). The primary theory note combines their reported results into information/error bounds for a terminal compressed monitor with declared approximation error and threshold degree.

## Independently checked arithmetic

MathCan/NoisyHorizon.lean imports only Init and uses the pinned repository Lean version. It verifies the following identities for all natural horizons T:

    noiseNum(T)+9^T=10^T,
    targetNum(T)+4*9^T=5*10^T,
    10*targetNum(T)<=targetNum(T+1).

The separately derived probability interpretation is that per-step crossover 1/20 produces effective crossover noiseNum(T)/(2*10^T). With an independently flipped balanced target at rate 1/10, the optimum coordinate-target error is targetNum(T)/10^(T+1).

The module checks the four-step numerator 23756 and five-step numerator 263804, and the positive-denominator comparisons establishing error <=1/4 at four steps and >1/4 at five steps. An integer midpoint lemma separates distinct posterior values after a common positive denominator is chosen. A generic decoder lemma proves that inputs requiring opposite answers cannot share a code. The finite arithmetic 2^2<8<=2^3 supports the separate Python certificate of eight posterior levels for majority7.

## Scope and CI

This module is compiled directly by the dedicated nhb01-noisy-horizon.yml workflow after the existing MathCan library builds. Its transitive axiom output is checked for sorryAx and ofReduceBool. The new module is a standalone checked companion; the main import file is unchanged.

The kernel file does not prove Shannon entropy inequalities, the probabilistic Fourier/noise identities, the general sensitivity theorem, or the optimality of a specific neural monitor. Those are supplied as handwritten derivations or conditional source statements in Compactification Theory. The complete finite probabilities use exact Fraction arithmetic; entropy comparisons in Python are numerical. No new model checkpoint is claimed.

The previous KSR MathCan PR #35 was merged before creating this branch. This new NHB work remains separate for review.

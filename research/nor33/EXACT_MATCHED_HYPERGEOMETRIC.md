# NOR-33: matched overlap, exact two-block hypergeometric counts

The [preregistered experiment](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/nor33-overlap-matched-transfer-20261117/research/nor33_overlap_matched_transfer/REGISTRATION.md) forces seven public ranking mechanisms to construct size-96 attack supports with precisely 0, 24, 48, 72, or 96 positions within the old tail ∪ magnitude ∪ lag union. It then selects radius-four attacks with exactly z=0,1,2,3,4 changed positions inside that union.

This module proves the conditional count identity for two attack-support blocks. If block A has a positions and a fixed audit inspects t_A of them, and block B has b positions and the audit inspects t_B, the number of matched attacks that **avoid the audit entirely** is

\[
\binom{a-t_A}{z}\binom{b-t_B}{r-z},
\]

among

\[
\binom{a}{z}\binom{b}{r-z}
\]

equally likely combinations. The ratio is the exact miss probability when the attacker samples uniformly inside each block before the audit's realized private coins. The theorem also establishes that two audit plans with the **same inspected counts within these exact same support blocks** have identical conditional miss and total counts. A finite roster of such audits retains that equality.

The result separates two sources of variation: exact overlap counts with the historical risk union and the policy's selection of *particular* coordinates within the matched support. Empirical family-specific residuals after fixed overlap identify effects not explained by the coarse historical union partition alone, such as curvature ranking's concentration within the old magnitude sector. All numerical residual effects remain empirical and source-conditional.

The original NOR-32 uniform-attack no-free-lunch result remains available. An explicit schedule-informed alternate-future witness is also retained. The proofs are over exact integer combinatorial counts using Lean 4.35's standard library and NOR-23/32 modules; they assume an authentic target-dependent coefficient witness and an attack fixed before the realized audit choice, without proving OS entropy quality, seed secrecy, or source-transfer generalization.

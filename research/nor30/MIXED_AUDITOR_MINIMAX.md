# NOR-30: minimax mixtures of exact witness auditors

This companion module formalizes the **finite arithmetic of mixing audit distributions** under a policy-aware attack chosen before the actual random audit coins. It extends NOR-26's arbitrary targeted-prefix bound and NOR-25's exact uniform-reserve coefficient counts.

[Applied prospective registration](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/nor30-sourceheldout-minimax-audit-20261117/research/nor30_minimax_audits/REGISTRATION.md) freezes the original NOR-26 7×7 cross-play at its archived SHA-256, an exhaustive 16-quantum seven-policy grid, a 12-source new heldout set, and eight preregistered policy-aware attacker classes. Training weights are frozen from prior evidence before any new source is generated.

The standalone Lean 4.35 module [MathCan/NOR30MixedAudit.lean](../../MathCan/NOR30MixedAudit.lean) proves:

- For any finite collection of arms, if arm i has a sound lower detection count L_i and an observed expected detection count H_i with H_i≥L_i, the mixed policy's weighted score satisfies \(\sum_i w_i H_i\ge\sum_i w_i L_i\). The policy-aware adversary may know the weights and select a fixed attack before the challenge coins.
- If the uniform auditor has positive integer weight and a positive registered exact floor, the complete mixture inherits a strictly positive lower bound regardless of the other arms' zeros.
- A concrete two-auditor/two-attack exact payoff game has zero minimax detection for **each** pure auditor and strictly higher payoff for an equal randomized mixture. An attacker observing the actual realized action can again evade in that game.
- Zero-weight arms cannot change the mixture's lower-bound or outcome numerator.

For the NOR-30 applied audit at k=16, r=4, the exact *ideal independent randomization* floor of a weight vector w on a 16-quantum simplex is

\[
\frac{w_{\rm uniform}}{16}\left(1-\frac{\binom{m-4}{16}}{\binom m{16}}\right)
+\sum_{u\in\{4,8,12\}}\frac{w_{\rm hybrid}(u)}{16}
\left(1-\frac{\binom{m-(16-u)-4}{u}}{\binom{m-(16-u)}{u}}\right).
\]

Risk-only arms have a zero source-independent floor. The constrained training grid ensures 2≤w_uniform≤12, and thus positive coverage against any fixed blind radius-four attack under the declared independent-sampling model.

The theorem does **not** prove the finite grid optimizer's empirical improvement, unrestricted game equilibrium, independence of public pseudorandom seeds, authenticity of external target values, or security against an attacker that sees the realized audit schedule. Those require the prospective applied experiment and its explicit timing/authentication assumptions.

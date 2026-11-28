# NOR-22: authenticated target fingerprints, modular collisions and the limits of public-only verification

Companion to the prospective [NOR-22 applied experiment](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor22-authenticated-future-commitments-20261116/research/nor22_authenticated_commitment) in Compactification-Theory.

NOR-21 proved that a public-only selector cannot distinguish two worlds with identical observed demonstrations and query INPUT but distinct hidden target outputs. A uniquely accepted candidate program remains insufficient to authenticate the **actual target** when someone may alter that target outside the generating family.

NOR-22 introduces an explicitly **trusted, exogenous, target-dependent commitment**. The commitment publisher has access to the true hidden target and produces one or two modular evaluations of its polynomial coefficients at a common nonzero point r=3:

\[
 H_p(Y)=\sum_{i=0}^{Q}Y_i\,3^i\bmod p,\qquad
 H_q(Y)=\sum_{i=0}^{Q}Y_i\,3^i\bmod q,
\]
with p=65537, q=65521 and Q=768 or 1536. The source verifier continues to determine a candidate only from the public RRC25 demonstrations and query input. A commitment check can then reject a prediction if the predicted polynomial's fingerprint differs from the authenticated true target fingerprint. A matching pair of short fingerprints is only a necessary condition for correctness.

The kernel-checked [MathCan/NOR22ModularFutureCommitments.lean](../../MathCan/NOR22ModularFutureCommitments.lean) proves:

- Any mismatch between a genuinely authenticated target fingerprint and a proposed output fingerprint proves the proposed output incorrect.
- A matching authenticated fingerprint implies correct output **only with an additional injectivity premise** on the relevant target domain.
- A candidate that fabricates its own alleged commitment always passes its own check; that comparison supplies no new information.
- A pair of different target worlds with identical complete public observations and identical two-component modular fingerprints cannot both be predicted correctly by any deterministic selector observing only those values.
- A p-sized scalar shift leaves residue modulo p unchanged, while the second modulus q distinguishes that scalar shift. A unit scalar change is detectable by the first modulus. A p·q shift is a distinct integer while leaving both residues unchanged.
- A terminal coefficient shift of Δ in a finite target series changes the exact polynomial evaluation at r=3 by Δ·3^Q at **every** finite query degree. Therefore the p-sized terminal edit has a collision in H_p and the p·q terminal edit has a collision in **both** H_p and H_q, at all finite degrees.

The formal theorem's terminal-weight function is recursively defined to match the coefficient evaluator and avoids relying on a toolchain-specific power rewrite. The modular shift collision remains source-independent.

## Original registered 12-source, 48-world experiment

The first [hosted applied CI run](https://github.com/MoralityLabAI/Compactification-Theory/actions/runs/43816319904) completed all registered source and policy checks. Twelve **distinct public inputs**, six at demonstration degree 512 and six at degree 1024, were generated from new seeds under offset 94322000. Each public case was paired with four possible hidden target worlds: valid output, plus one at the last coefficient, plus p at the last coefficient, plus p·q at the last coefficient. These are **48 paired counterfactual worlds representing only 12 independent source observations**.

| Hidden target world, 12 each | Public only | Trusted p | Trusted p and q | Forged p and q |
| --- | --- | --- | --- | --- |
| Original valid future | 12 correct | 12 correct | 12 correct | 12 correct |
| Last coefficient plus one | 12 false accepts | 12 abstain | 12 abstain | 12 false accepts |
| Last coefficient plus p=65537 | 12 false accepts | 12 false accepts | 12 abstain | 12 false accepts |
| Last coefficient plus p·q=4294049777 | 12 false accepts | 12 false accepts | 12 false accepts | 12 false accepts |

Every registered policy outcome matched the exact algebraic prediction. In the trusted-arm conditions the fingerprints are additional, target-dependent side information produced by a hypothetical honest publisher. The forged condition supplies candidate-generated checksums instead. The injected shifts are adversarially designed to reveal deterministic collisions, so these results are mathematical implementation checks rather than statistical claims of improved autonomous proof reasoning.

The original [public and authenticated-target-commitment fixture](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/nor22-authenticated-future-commitments-20261116/research/nor22_authenticated_commitment/results/nor22_original_hosted.zip) excludes full true target arrays and planted program identities. It deliberately includes trusted modular values computed from the true target. The original full result and source data are byte-locked in the applied research repository, with an independent audit that regenerated all 12 private programs **after public selections were frozen**, reconstructed 96 authentic modular commitment values and independently checked all 192 arm decisions.

These finite modular evaluations are **not cryptographic authentication**. Without a trustworthy publisher, the user of the verifier cannot assume that a commitment corresponds to the correct future. Even with authenticated fingerprints, a short modular collision remains possible and was explicitly demonstrated. Production safety would require a concrete trust model and a collision-resistant commitment scheme whose parameters match the threat model.

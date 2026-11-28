# NRF-09: matched-optimizer comparisons and robustness of eight-arm median margins

Date: 2026-11-15. Project-specific synthesis of elementary finite differences and order-statistic Lipschitz stability. No claim of new global mathematical priority.

## Exact depth-versus-update path identity

Let m(R,u) be the signed decoder objective margin J_supervised - median(J_random_0,...,J_random_7), where each random arm is a **complete** J_i=E_i+lambda L_i² and lambda>=0. Negative m favors supervised observation.

The original NRF-07 equal-state-visit comparison at 4096 visits compared m(32,16) to m(16,32), because batch size 8 yields visits=8 R u. A new matched-update comparison uses m(32,32) and m(16,32). The identity

```
m(32,16) - m(16,32)
 = [m(32,32) - m(16,32)] + [m(32,16) - m(32,32)]
```

separates the 4096-visit depth contrast into an equal-update comparison and the measured additional-training movement along the depth-32 path. It is an **exact arithmetic decomposition**, conditional on the chosen path. It does not uniquely identify a causal depth effect independently of all training-path interactions.

## Eight-arm median stability

For eight complete random-arm scores r_i and perturbed scores r_i', if |r_i'-r_i|<=delta for all i, their median defined by the average of sorted positions 4 and 5 obeys

```
|median8(r') - median8(r)| <= delta.
```

Proof: each order statistic is monotone in all eight coordinates. Comparing both vectors to coordinatewise shifts by +/-delta gives the inequality for each middle order statistic; averaging preserves the same bound. The constant 1 is sharp: adding delta to every score moves the median by exactly delta.

For a complete arm J=E+lambda L² with nonnegative leakages L,L', the exact drift estimate is

```
|J'-J| <= |E'-E| + lambda |L'-L| (2 L + |L'-L|).
```

Apply this to the supervised arm (bound delta_sup) and independently to all eight random arms (bounds delta_i). The signed margin obeys

```
|m'-m| <= delta_sup + max_i delta_i.
```

Thus |m|>delta_sup+max_i delta_i is a sufficient certificate that the decoder winner persists under the specified arm perturbations. The bound is conservative where changes cancel. Holding random-arm J fixed, supervised wins exactly when E_sup + lambda L_sup² < median8(random complete J).

## NRF-09 applied paired training

Six new seeds 131/137/139/149/151/157 were trained at R16 and R32 for 16 and 32 equal optimizer updates, using the same per-seed inputs, with fresh evaluation folds 7/8. Lambda=1 was selected in the earlier NRF-04 campaign.

At 32 updates, 6/6 R16 models favor supervised decoding and 5/6 R32 favor median random controls; the previously registered threshold of >=5/6 in each condition passes. Mean signed margins m were -0.1596746 (R16,32 updates), +0.2358013 (R32,16 updates) and +0.0560086 (R32,32 updates).

The mean equal-exposure gap is 0.3954759, with equal-update gap 0.2156832 and additional R32 training movement 0.1797927, equal to 45.46% of the gap along the chosen path. In the six matched seeds all equal-update depth differences have the same sign. An exact one-sided sign test gives 1/64 under its exchangeability/null assumptions, although the lambda choice and model family were exposed previously. The 5/6 random-win result at R32 has one-sided binomial p=7/64 against a 50% null.

The five still-random-winning R32 decoders at 32 steps need 3.7%–7.0% smaller local supervised leakage to reverse their rankings with MSE and random scores fixed. The sixth (seed 157) is already a narrow supervised win.

## Formal and experimental scope

- `MathCan/MatchedStepMargin.lean` uses Lean 4.35/Init to verify integer path equality and signed-margin stability under supplied drift bounds.
- `matched_step_margin.py` uses exact `Fraction` arithmetic for the full median and perturbation envelopes.
- `tests/test_matched_step_margin.py` covers 1,000 path equalities, 1,200 eight-arm median stability cases, 900 quadratic objective drift cases, 400 complete-arm margin perturbations and invalid domains.
- Lean does **not** formalize the real quadratic inequality, median order-statistic theorem, or the empirical model outcomes. They have written proofs and exact-rational tests.

Applied source and reports: MoralityLabAI/LoopedTransformers NRF-09 PR #88. The result pertains to one synthetic signed-permutation family and finite-sample Jacobian leakage, rather than a global quotient or improved reasoning capability.

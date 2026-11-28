# NOR-29: strict finite advantage of leaking audit entropy before commitment

Companion to the [NOR-29 prospective applied experiment](https://github.com/MoralityLabAI/Compactification-Theory/pull/197), built atop merged MathCan NOR-23 through NOR-28. The main theorem in [MathCan/NOR29EarlyEntropyGame.lean](../../MathCan/NOR29EarlyEntropyGame.lean) formalizes the cost of revealing the audit root before the attacker commits its changed-coordinate set.

## Two commitment information structures

Let Ω be a finite collection of possible roots. A root ω determines an entire batch B(ω) of 512 coordinate-audit schedules. Fix a nonnegative integer loss L(A,ω) counting how often a four-coordinate altered set A is detected in the batch.

An attacker committed before learning ω must choose one A for every possible root. An attacker that observes ω first may choose A(ω), but **must keep that chosen A(ω) fixed across the entire batch B(ω)**. If each chosen attack minimizes batch detection under that root, then pointwise

    L(A(ω),ω) ≤ L(A,ω)

for every fixed alternative A. Summing over the finite roots gives

    sum_ω L(A(ω),ω) ≤ sum_ω L(A,ω).

Consequently the minimum can move inside the expectation:

    E_ω [min_A L(A,ω)] ≤ min_A E_ω [L(A,ω)].

A strict two-root finite counterexample is kernel-checked: the root selects one of two possible checked coordinates, so each fixed early attack is detected once in the two equally represented roots; the root-aware attacker alters the other coordinate and is detected zero times.

This theorem assumes a true root-conditional best response. The applied NOR-29 attack uses 32 greedy tie-randomized approximate responses on the **same** realized 512-schedule batch. The empirical result therefore measures its achieved in-sample exposure reduction; its optimization quality is not globally certified by the theorem.

## Fixed-batch versus per-challenge response

A single attack A evades *all* schedules in a batch if and only if every altered coordinate is absent from every schedule. The Lean iff theorem expresses this exact condition without probabilistic approximations. It is stronger than evading any one schedule: an attacker choosing a fresh A after each single schedule can trivially select four unchecked positions whenever output length minus audit budget is at least four.

The NOR-28 commitment-binding hypothesis is inherited: if the original salted commitment already fixes A and the late root-aware choice B differs, then the new attack cannot open the original commitment under abstract binding. The finite mathematics proves consequences of the assumption rather than SHA-256 collision resistance.

## Applied experimental scope

NOR-29's 24 independent fresh source identities contain 32 blind pre-root committed attack sets each, 512 HMAC-SHA256 audits per source/policy and 32 late root-aware greedy attack sets per source and auditor, all of radius four. Three equal-budget policies compare a hybrid risk8/uniform8 reserve, a static risk16 list and uniform16 sampling. There are 2,359,296 distinct batch-fixed attack/auditor/trial decisions, with an additional 36,864 perfect-information per-schedule controls.

The original native RRC25 public verifier and external authentic exact target witness remain fixed. The OS root, HMAC pseudorandomness, SHA commitment binding and GitHub Actions chronology are computational/operational assumptions. Lean does not establish them, nor does it establish that the root-aware greedy attack finds the globally optimal batch response.

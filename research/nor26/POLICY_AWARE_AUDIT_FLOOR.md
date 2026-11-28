# NOR-26: finite policy-aware blind-attack bound

Companion to the registered seven-policy cross-play study in [Compactification-Theory NOR-26](https://github.com/MoralityLabAI/Compactification-Theory/pull/194). Builds on merged [MathCan NOR-25 #114](https://github.com/patrickdugan/MathCan/pull/114).

NOR-25 formally counted the undetected random-reserve subsets after one public-risk targeted prefix. NOR-26 allows a prior attacker to inspect the policy implementation and train an altered-coordinate set against 256 simulated challenge schedules, with that set frozen before the actual 512 evaluation schedules are sampled. The mathematical question is how much detection risk remains regardless of the arbitrary prefix distribution that the attacker knows.

The module [MathCan/NOR26PolicyAwareBlindAudit.lean](../../MathCan/NOR26PolicyAwareBlindAudit.lean) proves:

1. For every prefix whose remaining uninspected population has size N and contains r altered positions, exactly at most C(N-r,u) size-u uniform reserve schedules can miss the blind attack. If the targeted prefix already found a change, there are zero missed schedules.
2. The bound survives an arbitrary finite distribution of targeted-prefix outcomes: the sum of missed reserve schedules is at most the number of prefix outcomes times C(N-r,u). A randomized policy represented by repeated outcomes is included.
3. A complete audit schedule exposed to the attacker permits an exact-value transcript collision whenever at least one hidden coefficient remains unchecked, regardless of the risk-prefixed distribution.

Since each realized prefix has C(N,u) equally weighted size-u reserve schedules, the first two facts yield the detection floor

\[
  P(\mathrm{detect}\mid A\text{ fixed before challenge})
  \ge 1-\frac{\binom{N-r}{u}}{\binom{N}{u}}.
\]

For the registered 16-coordinate hybrid_50 policy, t=8 targeted slots, u=8 uniformly reserved slots, N=m-8 and r=4, where m=769 or 1537. The floor therefore becomes

\[
1-\frac{\binom{m-12}{8}}{\binom{m-8}{8}}.
\]

It is conditional on an ideal independent uniform reserve and a fixed r-coordinate attack chosen before the actual audit random draw. The separate fully schedule-informed attacker can alter unchecked coordinates after observing the chosen audit and attain zero detections. Authentic exact target-dependent witness values are additional information, assumed in the model. Public SHA-derived experiment seeds are reproducibility machinery rather than cryptographic secrecy.

The applied experiment should report the source-level self-play effects, the 7×7 policy/attack cross-play matrix, eight attack restarts per source/policy and 512 evaluation challenges. Repeated source-world-challenge outcomes are correlated. Numerical PASS/FAIL remains governed by the precommitted applied protocol.

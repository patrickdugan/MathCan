# NOR-26: calibration-aware prefix mixtures preserve a blind uniform-reserve floor

This formal companion extends [MathCan NOR-25](../../MathCan/NOR25UniformReserve.lean) and the applied [Compactification-Theory NOR-26](https://github.com/MoralityLabAI/Compactification-Theory/pull/194).

The attacker may select a fixed radius-r alteration set using the audit policy source code, training priors, and an unlimited calibration record. The attacked positions must be chosen **before** the actual independent challenge randomness. A targeted prefix T of t positions, possibly drawn from an arbitrary distribution depending on calibration, is followed by an **independent uniform reserve of u positions** chosen from the m-t unchecked coordinates.

For a given T, either A intersects T and every reserve detects, or A is disjoint and there are exactly C(m-t-r,u) undetected reserves among C(m-t,u) uniformly sampled reserves. Each conditional prefix world has at most this many misses. For any finite multiset of possible targeted prefixes, summing preserves the bound:

    number_of_missed_(prefix,reserve)_pairs
        <= number_of_prefixes * C(m-t-r,u).

The denominator is exactly number_of_prefixes * C(m-t,u). This implies the minimax lower bound on detection:

    detection >= 1 - C(m-t-r,u)/C(m-t,u)

for every policy-aware attack choice A satisfying the blind scheduling condition.

A rational mixture over targeted prefixes can be represented as a multiset with multiplicities equal to integerized mixture weights. A general real-valued mixture follows from conditioning on T and averaging the per-prefix bound. The Lean theorem proves the exact finite counting statements. It is independent of the calibration function and the learning algorithm.

The model assumes a genuine exact value witness for selected coefficients and independent reserve sampling; the public CI seeds serve reproduction only. NOR-25's verified schedule-visible counterexample survives, since any attacker choosing after observing all k sampled positions can alter four unchecked positions whenever m-k>=4.

The new Lean 4.35 standard-library module proves:
- exact per-prefix missed-reserve upper count;
- aggregate finite-mixture count inequality;
- the same inequality for any parameterized calibration-to-prefix distribution;
- exact count of all reserve schedules in the mixture.

The empirical NOR-26 study tests whether a greedy attacker fitted on 256 calibration schedules approaches the bound with 512 separately salted held-out audit schedules over 12 new source identities.

# NOR-27: how leaked audit randomness changes exact detection

Companion mathematics to the precommitted [NOR-27 applied seed-leakage experiment](https://github.com/MoralityLabAI/Compactification-Theory/pull/195), continuing MathCan's verified NOR-23, NOR-25, and NOR-26 coefficient auditing results.

A finite source-level verifier chooses a publicly determined t-coordinate risk prefix T, followed by u uniformly sampled reserve coordinates from the remaining m-t positions. A radius-r adversary seeks to alter indices outside the checked positions.

## Revealing actual sampled reserve coordinates

Suppose the attacker first observes ell coordinates drawn from that ordered reserve, and only then commits its altered set A outside T and the disclosed ell locations. The unobserved continuation has N=m-t-ell possibilities and u-ell remaining uniform samples. Because A has r locations in the undisclosed population, the number of ways to remain undetected is exactly

    C(m-t-ell-r, u-ell)

out of all

    C(m-t-ell, u-ell)

possible continuation subsets. Conditional detection is therefore

    1 - C(m-t-ell-r, u-ell) / C(m-t-ell, u-ell).

The formula assumes r≤m-t-ell and ell≤u, with an independently uniform conditional continuation, honest exact witness values, and a committed attack after the disclosed prefix. It gives the same probability for every admissible attack set A. When ell=u, all randomized reserve coordinates have been revealed, u-ell=0, and the attacker can always evade whenever r unchecked locations remain.

For the NOR-27 primary policy t=u=8, r=4, m∈{769,1537}, the expected conditional detection probabilities decrease as more of the realized reserve is revealed, eventually reaching zero.

## Leaking raw seed bits

Knowing b high bits of a secret 64-bit seed leaves 64-b possible unknown low bits under an ideal uniform seed distribution. That number alone is insufficient to deduce any sampling distribution conditional on the leaked prefix. A pathological sampler may depend only on one leaked bit, making the selected probe fully predictable even when an arbitrarily large private payload remains.

The theorem same_leaked_seed_prefix_same_attack_choice isolates the information restriction: two seeds with identical leaked observations force the same output from any deterministic attacker whose entire input is that observation. It does not imply a cryptographically secure distribution of audit continuations. This must be separately established for a deployed CSPRNG or carefully modeled as a synthetic benchmark.

## Lean verification

Module: [MathCan/NOR27SeedLeakage.lean](../../MathCan/NOR27SeedLeakage.lean), Lean 4.35 standard-library build.

- conditional_preview_exact_counts: exact missed and total continuation counts after a realized reserve-prefix leak
- zero_continuation_schedule_count and complete_preview_has_zero_additional_detection: full leakage leaves zero additional randomized detection
- same_leaked_seed_prefix_same_attack_choice: any selector restricted to the leakage value is constant on leakage fibers
- exposed_bit_can_determine_probe_with_hidden_seed_remaining: constructive insufficiency of a raw seed-entropy statement without a secure expansion assumption
- complete_schedule_disclosure_preserves_evasion: alternate hidden target with the same authenticated transcript whenever unchecked coordinates remain

The applied experiment compares previewing ell=0,2,4,6,8 actual reserve coordinates with revealing b=0,2,4 high bits of a SHA256-expanded 64-bit seed. The latter is a reproducible empirical toy with Python Random, not a new cryptographic hardness claim. It retains the external exact target witness assumption and prospective 12-source evaluation.

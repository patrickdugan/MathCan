# COL-06: exact donor availability for the native gym

For each core, group seeds by the conserved quotient, current branch and basin. At horizon h, let N_y count seeds in a group with future branch y in {1,3}. For each recipient n of label y, ordinary ordered distinct role assignments have N_(4-y)(N_y-1) choices. A stronger sham must share the recipient's entire future branch trace. Refine the partition (q,c) by successive pairs of the current cell and successor cell until it stabilizes. A cell containing n has size M_n within its group, so the stronger count is N_(4-y)(M_n-1). The stable cell is exactly equality of the complete future (q,c) trace: each refinement adds one future observation, and equal cell counts imply the refining partition has stabilized. The formula counts each ordered recipient/effect/sham triple once.

Independent local traversal and a second census using the canonical core agree on the reference aggregates below (the CI test also compares direct triple enumeration and pairwise trace replay on eight small parameters).

| Arithmetic horizon | Ordinary eligible roots | Ordinary triplets | Entire-trace sham roots | Entire-trace sham triplets |
| --- | ---: | ---: | ---: | ---: |
| 1 | 169/172 | 138645894 | 41/172 | 5942 |
| 2 | 169/172 | 138543826 | 38/172 | 5570 |

Across both horizons only 41 distinct roots support the stronger criterion (38 shared). These roots are exposed development sources; the count is below the 59 independent sham roots that would be needed even for a 95/95 sample-maximum null bound. Multiple triplets and horizons do not add independent roots. These are arithmetic availability counts, not neural sample sizes, model competence, or a calibrated sham distribution. Native partial prefix interventions are constructed states.

Reproduce: `python -m research.collatz_resonance.donor_census --check research/collatz_resonance/data/donor_census_summary.json`. The CLI emits all per-parameter rows.

## Native handoff

- [BPD #150](https://github.com/MoralityLabAI/BPD/pull/150): native two-pass Nanbeige runtime, source commit f1d489a000406e2d8732f4ea7a39e5473392efe2.
- [EvalMath #105](https://github.com/MoralityLabAI/EvalMath/pull/105): independent logit/label/score receipt verification.
- [LoopedTransformers #392](https://github.com/MoralityLabAI/LoopedTransformers/pull/392): offline activation geometry.
- [Compactification-Theory #301](https://github.com/MoralityLabAI/Compactification-Theory/pull/301): cross-root prefix-delta rank frontier.
- [DataGoblin #76](https://github.com/MoralityLabAI/DataGoblin/pull/76): verified arithmetic root quarantine.

The arithmetic controls in the merged Storyworld, SelfModels and RSITopology packages remain separate finite-system evidence. No native checkpoint outcomes or sealed roots are present in this census.

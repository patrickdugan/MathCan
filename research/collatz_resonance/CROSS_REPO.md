# Collatz application PR index

MathCan owns the definitions, general proofs, large census and arithmetic
prediction pilot in this directory. Companion changes add working adapters
at the research boundary of each repository. All PRs remain open for review.

| Repository | Pull request | Concrete addition |
| --- | --- | --- |
| MoralityLabAI/EvalMath | [#103](https://github.com/MoralityLabAI/EvalMath/pull/103) | Exact basin benchmark, conserved-observer ceilings, public parameter splits and prompt/gold exports |
| MoralityLabAI/DataGoblin | [#73](https://github.com/MoralityLabAI/DataGoblin/pull/73) | Unit-seed corpus generator, independent unaccelerated certificate verifier and admission gates |
| MoralityLabAI/LoopedTransformers | [#386](https://github.com/MoralityLabAI/LoopedTransformers/pull/386) | Finite history gym, seed decoder, matched shuffles and proposed neural protocol |
| MoralityLabAI/Compactification-Theory | [#300](https://github.com/MoralityLabAI/Compactification-Theory/pull/300) | Exact side-information frontier, code lengths and hash controls |
| MoralityLabAI/SelfModels | [#6](https://github.com/MoralityLabAI/SelfModels/pull/6) | Hidden arithmetic regime with action-dependent reward and exact inference controls |
| MoralityLabAI/RSITopology | [#11](https://github.com/MoralityLabAI/RSITopology/pull/11) | Invariant reachability obstructions, explicit closed sets and edit-aware verification |
| MoralityLabAI/GPTStoryworld | [#22](https://github.com/MoralityLabAI/GPTStoryworld/pull/22) | Native SWMD observation puzzle, official validation and unchanged reader replay |

## Shared contract

`collatz_core.py` has SHA-256
`24ff52171aedf890c33439896ab5e71de65d9b05d557ba61d162f3623aa5dbca`.
The observation, compression, regime, topology and story packages vendor
these bytes with source provenance. EvalMath and DataGoblin implement their
own checkers, permitting an independent comparison against this oracle.

The API validates positive d=1 mod 4, returns the exact next odd integer and
branch counts, enumerates complete small odd cores, labels each state by its
cycle minimum, and computes the <2,3> residue orbit when gcd(d,6)=1.
The small reference fixture includes d=1,5,13,29,73,97,217,313,577,1001.

## Delivery scope

All packages include executable checks and finite receipts or reproducible
generation commands. The learning-oriented PRs make their public development
status explicit. No neural training or paid compute accompanies these PRs.

GPTStoryworld remains a draft because its AGENTS.md requires a manual browser
playthrough. Official native validation, four Python tests and all 144 paths
through the unchanged JavaScript reader pass. A sandbox browser access block
prevented the required interactive check. Its README lists the remaining
playthrough steps.

EvalMath's inherited receipt suite includes an external DCF16 fixture at a
machine-specific OneDrive path. The new COL receipt has its own passing
path-filtered CI; the PR records the external-fixture limitation separately.

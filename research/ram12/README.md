# RAM-12: source-certified Lean goal-state traces

The original, frozen [protocol](PREREGISTRATION.md) precedes the first extraction. RAM-12 converts **76 previously twice-compiled, historical MathCan TRAIN proofs** into real, state-conditioned action examples while leaving the original tactic scripts and theorem statements unchanged.

## Native results

The first GitHub Actions attempt [43716654956](https://github.com/patrickdugan/MathCan/actions/runs/43716654956) built the exact old MathCan source but hit a tooling path error before proof scoring. The corrected, complete public [run 43716751350](https://github.com/patrickdugan/MathCan/actions/runs/43716751350) passed.

- Exact historical source: `MathCan@c84e2025334e9a967c1297425a490f98d5b3d189`, Lean 4.35.0
- Original 76 scripts, 22 old TRAIN theorem roots, 282 action occurrences
- **152 successful complete instrumented source compilations**, one independent pair per script
- **176 distinct exact-prefix goal contexts** and **230 unique positive prefix-to-action labels**
- Exact root split using the registered hash: 14 TRAIN roots / 3 DEV / 5 holdback; positive labels 137/31/62
- Same prefixes in different certified scripts have identical full printed goal states and visible definitions, checked by the native collector and independent artifact audit
- Every accepted original theorem passed the `propext` / `Classical.choice` / `Quot.sound` axiom gate, with no new axioms, `sorry` or `admit` in the emitted replacement proof
- The independent [receipt](receipts/independent_native_20261115.json) checked the exact source bytes, both compiler log hashes, 282 ordered markers, every positive label and per-case completion status

Artifact `ram12-pinned-native-lean-state-traces-43716751350`, ID `14162833338`, ZIP SHA256 `327dbd1382aca1a1c3c790e434341d582aafb85e5ad1b4f9b70ca84f21cae924`. The output `certified_state_action_labels.jsonl` has SHA256 `f744f779012c04d50a41798ee3805c91fbb8da922a174b09ccbde3310eb95e8f`.

## Training implications

These are **positive** demonstrated next actions from real goal states. A label says at least one complete proof continues from this action; another action is not assumed to fail. An exact-prefix audit remains necessary to distinguish these representations from the earlier goal-quotient false joins.

An independent check against the old RAM-08 dataset found 138/230 prefix-action pairs with matching recorded original contexts, leaving 92 additional witnessed positives. Of the 137 newly captured TRAIN positive pairs, 83 have at least one original compiler-rejected alternative in the matching exact-prefix context; 54 have no such original negative control. The original RAM-08 evaluation inputs were already used in training, so the RAM-12 internal root split is **retrospective** and cannot establish unseen theorem-family transfer.

The full native proof evidence, including prior RAM-11F source checks, supports positive state-conditioned imitation objectives. Recurrent-vs-flat search or new theorem competence still requires genuine held-out original source proof certification. The original RAM-08 PEF and RAM-10 original prospective evaluations remain **zero scored**.

## Reproduction

The public workflow [`ram12-native-state-traces.yml`](../../.github/workflows/ram12-native-state-traces.yml) checks out the original MathCan commit in an isolated directory. `Trace.lean` defines a read-only Lean tactic that logs the exact current compiler goal list before each frozen proof tactic; the collector requires two independent complete original-source compilations and returns an artifact with both source files, both logs, and exact proof-state labels. Run with the original public RAM-11F worklist and `leanprover/lean4:v4.35.0`. Software contracts: 6 tests passed in the original local Python implementation and public GitHub CI.

This research does not add theorem statements or change MathCan's main library.

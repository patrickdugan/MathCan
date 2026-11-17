# Recurrent observer and source-rule transfer research

**Current empirical manuscript:** [ROC-02–05 v0.4](ROC02_Observer_Causal_Update_v04_20261117.md), dated 17 November 2026.

Version 0.4 reports the registered **ROC-05A new-seed/new-permutation-pool training comparison** and **ROC-05B physically matched source-versus-hidden intervention** alongside the prior ROC-02–04 results. Both experiments use the original frozen ROC-05A first-run weights. All original training/checkpoint SHA-256 identities and source hashes are published.

ROC-05A replicates the transfer gain on independent training initializations and new source rules: four-rule accuracy **20.51%**, 512-rule accuracy **74.67%**, mean gain **+54.17 percentage points**, **6/6** positive model-seed directions, exact one-sided sign-flip **p=0.015625**. Complete eight-row table recovery averages **13.41%**, so the separate competence gate still fails.

ROC-05B's physical radius-0.20 intervention uses a train-only supervised rank-seven observer, legal early source-A table-row swaps, original model future logits and a hidden-L2-matched continuous input comparator. The mean observed minus softened-input target-margin gain is **−0.06805338**, with **0/6** positive seeds and exact p=1.0. Its primary causal gate fails despite 75.33% correctness on full legal changed-rule inputs. The 48 local ROC-01 observer cards are unclassified, with large incoming computed-change coupling.

The original ROC-02 source family-6/7 test remains unopened. ROC-04's previously reserved 384-table set was consumed in ROC-04B. ROC-05 has a separate new 384-table reserve consisting only of allocated identities, with **no input examples or labels generated or scored**.

**Earlier manuscripts:** [v0.3](ROC02_Observer_Causal_Update_v03_20261117.md), [v0.2](ROC02_Observer_Causal_Update_v02_20261117.md), [v0.1](ROC02_Observer_Causal_Update_v01_20261117.md). These versions are preserved unchanged.

## Independent arithmetic checks

- [ROC-02E](ROC02_primary_six_seed_v01.csv) and [exact sign-flip](roc02_primary_signflip_v01.py): negative calibration-family causal result p=0.375.
- [ROC-04A](ROC04A_primary_six_seed_v01.csv) and [verification](roc04a_primary_signflip_v01.py): exposed-dev gain p=0.015625.
- [ROC-04B](ROC04B_reserved_test_by_seed_v01.csv) and [verification](roc04b_reserved_signflip_v01.py): independent reserved-rule test p=0.015625.
- [ROC-05A original-run table](ROC05A_fresh_replication_by_seed_v01.csv) and [ROC-05B paired causal table](ROC05B_causal_primary_by_seed_v01.csv), checked together by [ROC-05 arithmetic verifier](roc05_fresh_and_causal_signflip_v01.py).

Run all checks with the Python standard library from the repository root:

```bash
python papers/roc02/roc02_primary_signflip_v01.py
python papers/roc02/roc04a_primary_signflip_v01.py
python papers/roc02/roc04b_reserved_signflip_v01.py
python papers/roc02/roc05_fresh_and_causal_signflip_v01.py
```

The [ROC-05B complete raw-null hosted replay](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44107680072) provides all 73,728 intervention records and 3,072 rank-matched null observations on the original twelve first-run weights. An additional independent null/empirical-tail/Holm [audit workflow](https://github.com/MoralityLabAI/LoopedTransformers/pull/165) checks the full geometry without new neural training.

Inference boundaries: ROC-05A evaluates a new exposed development pool, while ROC-05B selects its mechanism comparison after ROC-05A dev results were available. ROC-05B's softened input control is off the legal source manifold. Its negative physical-margin result concerns one frozen rank-7 projection and output horizon. A new independent rule-identity set and the complete ROC-01 intervention family remain distinct future gates.

# Recurrent observer and source-rule transfer research papers

**Current empirical manuscript:** [ROC-02–06 version 0.5](ROC02_Observer_Causal_Update_v05_20261125.md), 25 November 2026.

ROC-06A uses a **train-only counterfactual-gradient rank-seven observer** on the twelve original frozen ROC-05A models. It improves observed-source hidden margin gain by +0.011409 over supervised rank seven across all six high-diversity seeds. The equal-L2 softened-input comparator remains stronger: gradient minus best reference **−0.056644**, 0/6 positive seeds, one-sided exact p=1.0. The registered physical mechanism gate fails, with all 72 local observer cards unclassified. The study uses 256 already exposed development examples per model; ROC-05's 384 reserved test identities remain unopened.

**Earlier empirical manuscript:** [version 0.4](ROC02_Observer_Causal_Update_v04_20261117.md), 17 November 2026. It includes the ROC-05A source-diversity training success and ROC-05B matched physical observer failure. The v0.1–v0.4 manuscripts are preserved as dated historical sources.

Version 0.4 integrates the original ROC-02B/C/E observer-geometry and causal tests, ROC-03A/B competence diagnosis, and both ROC-04A exposed-development and ROC-04B independently reserved-permutation confirmation. The latest follow-ups are:

- **ROC-05A, fresh source and model seeds:** 512-rule training improves newly exposed development answer accuracy from 20.51% to 74.67% at a matched architecture/optimizer budget, with six positive paired model seeds and exact one-sided p=0.015625. Primary replication PASS. The separately registered complete eight-row table competence gate FAILS, with 13.41% mean exact table recovery. A second computational replay had the same result direction but only 2/12 byte-identical checkpoint binaries; the first complete run is canonical.
- **ROC-05B, first-run original models frozen:** at physical midpoint L2 radius 0.20 the high-diversity rank-seven source-observed hidden-steering margin gain is +0.11797, while the off-manifold softened input comparator yields +0.18602. Observed-minus-input mean is −0.0680534, with 0/6 positive seeds and one-sided exact p=1.0. The registered causal gate FAILS; 48/48 rank/null local observer cards are unclassified. The full legal source-rule edit still yields 75.33% correct changed answers.
- The 384 ROC-05 reserved test **table identities remain ungenerated as input cases**, and the original ROC-02 source-family-6/7 examples remain sealed. ROC-04B's earlier 384-rule reserved test has already been consumed for its original trained cohort.

**Preserved earlier versions:** [v0.3 independent ROC-04B](ROC02_Observer_Causal_Update_v03_20261117.md), [v0.2 ROC-04A development](ROC02_Observer_Causal_Update_v02_20261117.md), and [v0.1 ROC-02/03](ROC02_Observer_Causal_Update_v01_20261117.md).

## Independent public arithmetic checks

- [ROC-02E original six-seed table](ROC02_primary_six_seed_v01.csv) and [exact arithmetic checker](roc02_primary_signflip_v01.py).
- [ROC-04A development table](ROC04A_primary_six_seed_v01.csv) and [exact checker](roc04a_primary_signflip_v01.py).
- [ROC-04B reserved-test table](ROC04B_reserved_test_by_seed_v01.csv) and [exact checker](roc04b_reserved_signflip_v01.py).
- [ROC-05A fresh-source first-run table](ROC05A_fresh_seed_primary_v01.csv) and [ROC-05B matched causal table](ROC05B_matched_causal_primary_v01.csv), both covered by the [combined exact/sha verifier](roc05a_b_primary_audit_v01.py).

Run from MathCan repository root:

```bash
python papers/roc02/roc02_primary_signflip_v01.py
python papers/roc02/roc04a_primary_signflip_v01.py
python papers/roc02/roc04b_reserved_signflip_v01.py
python papers/roc02/roc05a_b_primary_audit_v01.py
```

The [ROC-06A six-seed primary CSV](ROC06A_gradient_primary_by_seed_v01.csv) and [exact conservative max-of-two reference verifier](roc06a_gradient_primary_signflip_v01.py) reproduce the registered gradient mechanism FAIL from the original LoopedTransformers Git blob.

Run the ROC-06A verifier from the repository root:

```bash
python papers/roc02/roc06a_gradient_primary_signflip_v01.py
```

The checks use Python's standard library and retain original Git blob SHA-1 provenance for the copied empirical CSVs.

The [ROC-05B complete raw-null addendum](ROC05B_FULL_NULL_REPRODUCIBILITY_ADDENDUM.md) records the separately hosted 3,072 rank-matched null rows, the independent 288-test empirical/Holm audit, and both original/expanded SHA-pinned 69-file causal archives. All preserve the original six-seed negative mechanism finding. Model-weight and per-case replay receipts are published separately in [LoopedTransformers ROC-05A #162](https://github.com/MoralityLabAI/LoopedTransformers/pull/162) and [ROC-05B #163](https://github.com/MoralityLabAI/LoopedTransformers/pull/163), with the successful original-model full causal audit [run #44107080894](https://github.com/MoralityLabAI/LoopedTransformers/actions/runs/44107080894).

The empirical studies concern eight-label synthetic rule-binding tasks with an explicitly routed query. Complete ROC-01 five-mechanism identification, an independently reserved ROC-05 test, and broader model-family comparisons require separate prospectively locked experiments.

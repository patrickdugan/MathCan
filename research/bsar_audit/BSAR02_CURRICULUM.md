# BSA-R six-round theorem-boundary curriculum (BSAR-02)

The initial five-theorem audit is in MathCan main via PR #165. This follow-up pin expands the static catalogue to **129 declarations** from all six BSA-R Lean round files at [`80c62433`](https://github.com/VivienSweetbrier/bsa-r/tree/80c62433b0eb671175bd8d6169822d3ebd922b60).

`six_round_catalog.json` records each declaration's source file, line, full signature, named hypotheses, and type-domain hints. The round totals are 10, 22, 17, 17, 27, 36. The extractor looked for anchored `theorem` signatures ending at `:= by` and may omit other declaration forms. None of these 129 signatures contains an explicit analytic PDE type. Step 2 includes the abstract type `R`, which is deliberately separate from `Real`; other declarations use integer or combinatorial objects. This is a **source-text audit**, pending native Lean compilation and semantic analysis.

Generate the supervised corpus locally:

```sh
python -m research.bsar_audit.boundary_curriculum --output-dir /tmp/bsar-boundary
python -m unittest tests.test_bsar_boundary_curriculum -v
```

The corpus trains a proof-review policy to identify named hypotheses, spot improper leaps from algebraic inequalities to Navier–Stokes regularity, and demand kernel evidence. It includes positive controls for signatures genuinely present in source. The output is labelled `STATIC_LEAN_SOURCE_ONLY`. The examples are **synthetic supervision**, with no claims about model accuracy or kernel verification.

## Split contract

- Train uses Steps 2–5.
- Dev uses Step 6.
- Test uses Step 7.
- If a lemma name appears in multiple rounds, the generator assigns it to the latest split and suppresses the earlier duplicates, preventing cross-split name leakage.
- Every output has a pinned source line, statement, label and short rationale. Rebuilds are deterministic under a seed.

Evaluation should report precision and recall for `UNSUPPORTED_PDE_LIFT`, `MISSING_PREMISE`, and `KERNEL_CHECK_REQUIRED` on the completely held-out Step 7 declarations. The next stronger test is *unseen mathematical frameworks*: fresh MathCan formal papers with statement-level audits and genuinely kernel-checked proofs. All labels in this corpus describe the claim scope of published source text and must not be treated as independent proof certificates.

# RAM-14 | Structural tactic-generation diagnostic, registered after RAM-13 results

**Date:** 16 November 2026. **Scientific status: POSTHOC DIAGNOSTIC.**

## Background and provenance

RAM-13's frozen [fresh-source theorem evaluation](https://github.com/MoralityLabAI/LoopedTransformers/pull/105) found 0/2 certified original `GramianTransfer` theorems under each of the nine primary policies and four secondary policies, with **156 original policy/theorem cases** and **114 independent proof certificates** across the entire cohort. The original two Gramian cases were selected before any RAM-13 inference. This follow-up was designed **after their failure and after their public reference proof bodies were inspected**. Its results are excluded from RAM-13's registered score and cannot be called new held-out generalization.

Pinned source **`patrickdugan/MathCan@f427e0ef4a61093304d12ca2c0dc943d8d2429e5`**, Lean **4.35.0**, original `MathCan/GramianTransfer.lean` blob SHA-1 `f07e99a3f27acba22c2c0c6b3f675a68ab774ab2`. The two diagnostic declarations are `transport_iterate` and `observable_transport`. Their original reference proofs are forbidden as candidate scripts and are replaced completely during scoring.

## Hypothesis and baseline

The original RAM-08/RAM-13 20-family source-visible grammar permits `induction_list` only for list variables and allows `rw_local` only against local hypotheses. The first difficult theorem requires reasoning by induction over `n : Nat`; the second uses an earlier source-visible theorem to rewrite the recurrence. The missing **type-directed Nat induction** and **previously declared lemma reference** are concrete coverage deficiencies. This is a *structural diagnosis* based on an already observed failure.

Keep the original 20-family candidate grammar immutable for comparison. Add **only**:

1. `induction_nat`: apply bounded induction to locally visible Nat variables, optionally generalizing another locally printed variable. Generate two fixed proof macros per (Nat, state) pair: a one-line `induction ... <;> simp_all [...] ` and `induction ... <;> simp [...] `. The simplification lemmas are chosen from **visible theorem-statement identifiers, previous source declarations and context-typed inverse-law fields**; no target theorem proof text is read by the generator.
2. `simp_prior`: simplify using at most two previously declared theorem names whose names or statement identifiers overlap the target goal; add source-context inverse-law fields from structure binder types.
3. `rewrite_prior`: `rw [previous_lemma]` or `simp [previous_lemma, inverse_field]` using only source declarations before the target. Never use a theorem declared after the target.

The implementation may use a small bounded set of fixed generic tactic templates, but **every resulting source must independently compile** to count. For audit, report each generated tactic, its provenance (binder, earlier declaration or explicit field), the action grammar family, full compiled source SHA and both Lean returns. Limit to 48 total candidate scripts per target (at most 16 per family) and at most 15 seconds for each independent whole-source Lean compilation. No new definitions or lemmas are inserted into the target source.

## Experimental procedure

- Verify the exact pinned source commit, blob SHA, original Lean toolchain, and the declaration order before generating candidates.
- Generate every permitted tactic using only the pre-target declaration text and target theorem **statement**. A separate auditor may look at original proofs to explain errors, but the generator must not consume them. Use a one-shot generated `by` proof, no source oracle prefix and no manual fallback proof.
- Create each test source in a fresh project-local scratch path, replacing the complete original target proof. Do not modify the original source checkout.
- Compile once and, if accepted, compile a second time into a byte-identical independent source path; both must pass the `#print axioms` gate allowing only `propext`, `Classical.choice`, `Quot.sound`, or no axioms. An unaccepted, timed-out or abnormal case never earns proof credit.
- Report original RAM-13 baseline coverage (0/2) as **historical comparator**. Do not report retrospective improvements as independent model transfer. Count actual compiler invocations and preserve all failed candidate logs.
- Include positive and negative unit tests covering no source-proof substring leakage, no future-lemma selection, binder derivation, valid generated tactic syntax, deterministic ordering, and required double compilation.

## Future prospective campaign

Use any successful general grammar rules to preregister on **entirely different unopened source modules**, including matched symbolic controls and recurrent/flat rankers, with a model freeze before source access. Avoid selecting future test cohorts using the present two theorem results. Source code, candidate lists, source references, resource costs and all negative outcomes stay in auditable records. No training, private checkpoint export, merge, or spending is authorized by this diagnostic itself.

# RHD-10B: within-family correction-policy audit

**Parent PR:** RHD-10 #169. **Mathematics:** finite E = Q(zeta_20), ell = 29 first-layer arithmetic; 3,364 root episodes with 1–3 injected faults. **Proof boundary:** neither a trained neural RLT nor an automorphic TyEll witness.

## Evaluation contract

The original RHD-10 archive is a **teacher rollout dataset**. The rhd10_policy_eval.py script fits a frequency-table behavioral cloning baseline using **only train-split teacher transitions**. Validation and test policy calls receive a whitelist of root_id, selected factor, source prime, local probe and a candidate snapshot, plus separately requested verifier observations. The evaluator strips all expected answers, gold terminal states, teacher step counts, teacher actions, oracle success bits and teacher verifier feedback from the policy's view. Independent tests poison held-out oracle fields and assert byte-identical results.

The finite generator is public, and all splits share the same field, prime and known fault grammar. Report all results as **within-family synthetic repairs**. A SHA-256 split over distinct (factor,a,b) roots prevents row duplication, yet cannot establish transfer across primes or unseen mathematical structures. Deterministic root identifiers and source code make this an auditable benchmark, not a sealed challenge.

## Policy-visible verifier modes

| Mode | Observations | Action budget | Billing |
| --- | --- | --- | --- |
| sparse_one_step | One failing gate | One correction, then final check | 2 queries per episode |
| sparse_recurrent | One failing gate on each round | At most three corrections | 2–4 queries |
| full_open_loop | All failing gates initially | Apply all repairs, then check | 2 queries per episode |

The **full open-loop baseline is mandatory**. RHD-10's original verifier exposes every defect simultaneously. When independently repairable faults are observable at once, fresh verifier calls after each edit can cost more than executing the initial plan. Comparing solely one-step and multi-step budgets would falsely credit recurrence with an information advantage.

The privileged_rule_ceiling calls the exact RHD-10 arithmetic suggestion function and is explicitly marked as a privileged control. The trained_frequency policy is a fitted lookup policy. Repeated application of that policy with new feedback is an iterative correction procedure, **not** evidence that a neural recurrent network has learned to reason. A future RLT checkpoint must be scored with the same observation and billing interface.

Every reported success is a *final verifier pass*. The invalid_edits metric counts edits that failed to reduce the total number of finite gate violations. Independently computed scoring checks do not enter the **policy-visible verifier call** denominator; the report says so. The stop_accuracy metric records whether a policy stops with all finite gates satisfied. The primary efficiency metric is 100 × solved_episodes / policy_visible_verifier_calls.

## Reproduction

~~~bash
python -m unittest tests.test_rhd09_local_character tests.test_rhd10_rank_one_repair tests.test_rhd10_policy_eval -v
python -m research.rh_proof_distillation.rhd10_policy_eval --output rhd10/policy_eval.json
~~~

CI uploads the report and its companion SHA-256 receipt. Inspect the test and validation scores independently. The report is deterministically regenerated from the code. No hand-entered score is used as a proof claim.

## Next generalization gate

Derive an independent Q(zeta_24), p=5 norm-character benchmark: Phi_24(X)=X^8-X^4+1 splits into four distinct irreducible degree-two factors modulo 5. Derive and test the degree-two Hensel lifts modulo 25, the exact norm/trace exponent identity and the four ramified places. Keep this family completely outside training. Measure transfer and abstention on failed probes before promoting an RLT checkpoint.

The automorphic work remains separate. Current MathCan Init eigenline theorems concern integer-valued abstract characters. The target TyEll needs an actual complex-valued adelic eigenvector and representations. The source-pinned SphOffU versus GenTy exceptional-set requirements require their own proof-interface reconciliation.

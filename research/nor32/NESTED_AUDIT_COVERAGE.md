# NOR-32: nested audit coverage and coupon-collector scaling

Formal companion to the prospective [NOR-32 Compactification-Theory experiment](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/nor32-nested-depth-audit-20261117/research/nor32_nested_audit_depth).

## Exact finite Lean results

Module [MathCan/NOR32NestedAuditCoverage.lean](../../MathCan/NOR32NestedAuditCoverage.lean) extends the NOR29–31 fixed-batch audit game.

- evades_append_iff: a fixed altered set evades a concatenated batch exactly when it evades both sub-batches.
- never_inspected_at_longer_depth_was_unseen_earlier: every coordinate untouched in an extended batch was untouched in its prefix.
- four_coordinate_evasion_feasibility_monotone and impossible_four_coordinate_evasion_stays_impossible: the existence of four DISTINCT never-inspected altered coordinates cannot reappear after the batch grows.
- total_detection_count_monotone_under_nested_audits: for a fixed attack, adding nonnegative detection costs cannot decrease its TOTAL detected audit count.
- any_menu_lower_bound_survives_extra_audits: a uniform lower bound over every attack from a fixed menu survives added scans, proving the minimum TOTAL hit count over that menu cannot decrease.
- detection_fraction_need_not_increase: explicit finite counterexample, one hit of one scan versus one hit of two, showing detection FRACTION need not rise monotonically.

These statements are deterministic and independent of how the audit schedules were sampled. The last two distinguish total hit counts from fractional detection, especially as the root-aware attacker is allowed to choose a new fixed attack per new batch depth.

## Ideal uniform coupon-collector calculation

At output length m, hybrid risk8/uniform8 audits the same eight public trained-risk positions in every challenge and samples eight distinct positions from the remaining N=m−8 each time. For any one of these N positions, independent ideal random sampling leaves it uninspected with probability 1−8/N on one challenge. By conditional independence across n challenges, the probability it remains untouched is (1−8/N)^n. Summing N coordinate indicators yields the exact expected never-inspected count

    E[U_n] = N * (1−8/N)^n.

The full uniform16 control has E[U_n]=m(1−16/m)^n. The deterministic static16 arm leaves exactly m−16 untouched regardless of n.

For a batch-fixed radius-four attacker, a completely undetectable attack across all n audits exists if and only if U_n≥4, assuming nonzero changes and an exact target coefficient witness. This is a finite coverage criterion, directly formalized by the Lean feasibility theorem. Under the same ideal independent sampling model, Markov gives

    Pr(U_n≥4) ≤ E[U_n]/4.

The bound is a conservative probability guarantee on the existence of four completely unseen positions. Even when U_n<4, a known-root attacker can choose four rarely inspected coordinates and suppress its per-challenge detection rate; the Lean fraction counterexample shows why this rate need not be monotone.

## Applied experiment and assumptions

The registered applied NOR-32 compares 24 new source-distinct RRC25 public problems, nested batch lengths 512, 1024, 1536 and 2048, three equal-budget auditors and two attacker regimes: independently calibrated precommit attacks and actual-root-aware attacks using the same 32 greedy tie restarts and the first n schedule draws. Both independent calibration and actual evaluation roots are fresh 256-bit OS values in separate dependent jobs. The direct coverage gate compares m=1537 hybrid four-unseen feasibility between n=512 and n=2048.

Lean proves finite set and loss structure under its declared type hypotheses; the analytic expectation assumes ideal independent uniform draws. HMAC-SHA256 pseudorandomness, OS entropy freshness, SHA commitment binding, CI runner integrity and authentic exact target-coefficient witnesses remain external assumptions, rather than mathematical consequences of the finite theorems.

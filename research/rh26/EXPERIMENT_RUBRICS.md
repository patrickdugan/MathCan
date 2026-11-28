# RH-26: bounded mathematical extraction rubrics

Status: PROTOCOL ONLY (2026-11-23). No upstream theorem independently rechecked here; no mathematical extraction or experiment has passed. This file is the durable resumption checkpoint.

## Targets and provenance

Upstream: https://github.com/leanprover-community/riemann-hypothesis
- Inspect exact upstream git SHA before each extraction; record it below in a run ledger.
- Read README, `src/Main.lean`, `src/Statements.lean`, `verification/NOTES.md` and the one-hop imports actually needed. Avoid cloning/building the entire proof on local equipment.
- Upstream main toolchain observed: `leanprover/lean4:v4.37.0-rc1`; original submission used v4.33.1. MathCan pinned to v4.35.0 as of this rubric. Keep checkouts and dependency caches isolated.
- Original submission is published without an explicit license. Cite paths and theorem names; independently author commentary and fresh Lean lemmas. Avoid copying proof source into MathCan.
- The top-level theorem `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf` derives from `UpperTheory.FinalTheorems.everyCharacter`; `riemannHypothesis` follows by `Claim.zeta`. This is the first dependency boundary.

## Session limits and stop rules (anti-context-overflow)

1. One experiment per session. Read at most 8 upstream files, 250 lines per file, 1,200 aggregate lines, and 2 dependency hops. Prefer names, theorem signatures, imports, and exact line ranges to complete proofs.
2. Produce a <=1,000-word checkpoint after each session in `research/rh26/LEDGER.md` (create upon first actual run): upstream SHA; inspected file/line ranges; precise claim; evidence; unresolved obligations; next exact paths; resource use; disposition.
3. Never recursively scan the 175k-file original formalization, run a full local `lake build` of upstream, or import upstream wholesale into MathCan. Larger searches require their own bounded CI/cloud job with fixed output caps and published receipts.
4. If the claim cannot be traced within the budget, register BLOCKED with the missing symbols and stop. A guessed identification is not evidence.
5. If source changed, pin a new SHA and separately report the delta. Keep previously frozen receipts unchanged.
6. Maintain a strict distinction: formally checked theorem / faithful mathematical paraphrase / proposed analogy / speculative application.

## Common acceptance rubric

For each RH-26A..E: pre-register the question, exact source SHA and theorem anchors, a competing/null explanation, a measurable pass criterion, minimum falsifier, time/CPU/RAM cap, and artifact destination. Require two reviewers or checks for mathematics: a conventional mathematical argument and an independent Lean kernel run where feasible. `sorry`, custom axioms, `unsafe`, opaque trusted oracle shortcuts, or cached upstream oleans alone do not qualify as a kernel-verified new theorem. Keep the MathCan toolchain pinned unless a separate CI matrix establishes compatibility.

## RH-26A: dependency compression of final nonvanishing

Question: What is the smallest intelligible chain from `UpperTheory.FinalTheorems.everyCharacter` to an analytic/arithmetic input?

Procedure: inspect `src/Main.lean`, `src/Statements.lean`, then only imports that feed `everyCharacter`; construct a symbol-level directed acyclic graph with theorem signatures and named assumptions, each edge backed by a file/line reference. Stop at two hops for the first pass.

Pass: a complete top-level graph for the five headline theorem statements, explicit distinction between GRH and RH, and at least one leaf with precise mathematical hypotheses. Fail: vague thematic summaries without source anchors.

Artifact: `research/rh26/RH26A_DEPENDENCIES.md`.

## RH-26B: theta-lift multiplicity isolation

Question: Which exact lemma uses theta lifts or associated automorphic constructions to obtain a quantitative vanishing/multiplicity bound?

Procedure: find exact declarations by restricted symbol/path search; identify the operator, input/output spaces, normalizations, assumptions and inequality; trace one use of that lemma. Formulate a smaller abstract proposition and state every assumption it needs.

Pass: a source-cited lemma, faithful mathematical statement, one checked toy example or independently derived special case. If no direct theta-lift chain is found under the scope limit, log UNSOURCED rather than claim a connection.

Artifact: `research/rh26/RH26B_THETA_LIFTS.md`.

## RH-26C: prime-sum asymptotic gate

Question: Does the formal argument contain a bound genuinely of the form `E(X,m) <= C1 X/m + C2 m`, and under which ranges and implied constants?

Procedure: identify the actual theorem and hypotheses; record whether `m` is integer, restricted by X, and whether constants depend on m, X or arithmetic data. Independently show the conditional minimizer `m ≍ sqrt(X)` (for positive fixed constants; rounding and domain constraints explicit).

Pass: faithful theorem pointer plus exact constants/dependencies, or a recorded counterexample to the proposed heuristic. A generic calculus optimization alone is tagged TOY and does not establish the upstream bound.

Artifact: `research/rh26/RH26C_PRIME_SUMS.md`.

## RH-26D: spectral / arithmetic holonomy bridge

Question: Can a precisely defined transfer or theta operator from RH-26B be compared to a MathCan arithmetic-holonomy operator without changing domains or pretending quantum hardware establishes RH?

Procedure: specify spaces, inner products, composition and any trace/determinant; prove one finite-dimensional test identity, then identify what fails to extend to the analytic setting. Compare to AHR-QPU-01 only as a separate exploratory analogy.

Pass: exact operator dictionary with one independently verified identity and an explicit obstruction or missing theorem. A similarity of vocabulary does not count.

Artifact: `research/rh26/RH26D_OPERATOR_BRIDGE.md`.

## RH-26E: minimal independent Lean checks

Question: Can MathCan v4.35.0 verify a fresh nontrivial, dependency-light lemma motivated by RH-26A..D?

Procedure: implement a mathematical lemma from scratch in `research/rh26/lean/` (or normal MathCan Lean source path if required by lake); use the pinned MathCan CI; record `#print axioms` of the new theorem, proof audit, imports, runtime and memory.

Pass: green pinned kernel job, only permitted foundational axioms (`propext`, `Classical.choice`, `Quot.sound` where actually needed), reproducible source and no admissions. A toy lemma must be labeled toy.

Artifact: `research/rh26/RH26E_LEAN_CHECKS.md` plus code.

## Priority / execution order

0. Preserve this protocol on a branch and open a draft PR.
1. RH-26A first, strictly bounded, before making claims about the machinery.
2. RH-26C and RH-26B only after precise source anchors have been established.
3. RH-26E formalizes the smallest independently useful lemma.
4. RH-26D only when a mathematically defined operator is available.

## Ledger skeleton

```text
RUN ID:
UTC date:
Upstream commit SHA:
MathCan commit SHA:
Track:
Files and line ranges inspected (<=8; <=1200 lines):
Claim / theorem signature:
Evidence / independent verification:
Competing interpretation / falsifier:
Time / compute / memory:
Status: PASS | FAIL | BLOCKED | TOY | UNSOURCED
Next exact symbol/file to inspect:
```

## Resume instruction for another agent

Start by reading ONLY this file and the most recent `research/rh26/LEDGER.md` entry if it exists. Continue at RH-26A, pin upstream SHA, inspect no more than the stated bounded files/lines, write a checkpoint, commit evidence and exit. Preserve the main MathCan branch and avoid long upstream-context imports.

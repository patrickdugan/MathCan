# AUTHQ-01: observation-relative authorization

**Status:** candidate Lean proof, awaiting the destination repository's Lean 4.35.0 CI. Mathematical scope: a deterministic authorization predicate and an observation function.

For world `s`, action `a`, observation `o(s)`, and supplied authorization predicate `Auth(s,a)`, an observation-only classifier exists if and only if

`o(s) = o(t) => Auth(s,a) = Auth(t,a)` for all states, pairs and actions,

provided the observation is surjective onto its declared output type. The equivalence is proved constructively except for choosing a representative of each observation fibre. Equal visible observations and opposite duties force *any* deterministic classifier to err on at least one member of the pair. With equal independent assignment to the two worlds, accuracy is at most one half for the binary fixed-action decision; that probabilistic interpretation is a paper-level consequence, not a Lean probability theorem.

The Lean file `MathCan/AuthorizationQuotient.lean` includes a two-state collision witness and a fully informative inspection witness. A coarsening lemma formalizes that discarding information cannot repair an authorization collision.

**Connection to current repositories**

- `MathCan/ObservableQuotient.lean` factors state transitions through observation fibres. AUTHQ-01 factors *authorization* through the same concept.
- `MathCan/NOR21ObservationCompleteness.lean` gives a generic impossibility result for different correct futures with the same public observations.
- `MoralityLabAI/Control-Harness` can construct matched authorization twins and offer an authenticated inspection action.
- `MoralityLabAI/EvalMath` should measure action, refusal and error independently, using FSI-01 clusters and a sealed evaluation set.
- `sadasant/organon` separates Capability, Permission, and PermissionExercise. Here `Auth` is externally supplied and must be mapped to an explicitly selected institutional predicate; this theorem never decides which institution is legitimate.

**Next experimental gate:** build paired authorization worlds sharing the uninspected view, then add a trustworthy inspection that makes the pivotal fact visible. Compare the same frozen controller under hidden versus revealed conditions. Retain always-abstain, always-retain, and signed-rule lookup baselines. Do not promote a result before cluster-level power and sealed readout checks.

## AUTHQ-02: information gained per inspected root pair

The new `PairedDecision` Lean definitions count retained proposals in authorized and unauthorized worlds of the same public-observation pair. When each unaudited pair has identical decisions under the two permission truths, Lean's proposed `paired_inspection_at_most_budget` proves

```
retained_authorized <= retained_unauthorized + inspected_pairs <= retained_unauthorized + B.
```

For N equally weighted paired worlds and binary retention choices, the difference `J = TPR - FPR` therefore satisfies `J <= B/N` for a maximum of B audited root pairs. The proof is combinatorial and uses no probability model. It counts one *pair* as inspected if either counterfactual's decision can depend on its audit; the ECA-01 symmetric registered experiment audits both worlds of a selected root pair.

### First registered application (synthetic only)

[Control-Harness ECA-01, prospective CI #44131080443](https://github.com/MoralityLabAI/Control-Harness/actions/runs/44131080443) scored 64 independent-seeded counterfactual root pairs, 28 with a common issuer and 36 with distinct issuers. Its code and protocol were frozen at `bc0ebeb053c5038a2abb20444effda235f7dc060` before the root entropy was sampled.

- Native attested two-key: 64 authorized retains, 64 unauthorized retains; `J=0`.
- Lineage-only: 36 authorized retains and 36 unauthorized retains, 56 escalations; `J=0`.
- Audit after lineage escalation: 64 authorized retains and 36 unauthorized retains. Exactly 28 root pairs were inspected (56 individual audit calls), giving `J=(64-36)/64=28/64=7/16`. This saturates AUTHQ-02's finite budget bound.
- Audit all: 64 authorized retains and 0 unauthorized retains. All 64 pairs were inspected (128 individual audit calls), giving `J=1` and again saturating the bound.
- Always-remove and always-escalate control arms both have `J=0`, despite zero false authorizations; their usefulness is separately measured.

The simulator's audit reads the planted authorization truth from a host-owned oracle and authenticates it using a synthetic HMAC key. Under this deliberately complete inspection, correct decisions are guaranteed by construction. The numeric agreement checks the experimental encoding of the theorem; it gives no evidence that a deployed auditor has such access, that different real issuers are independent, or that a learned controller will request the right evidence. ECA-01's EvalMath manifest explicitly withholds paired-label exchangeability.

This update is a downstream research crosswalk, not a dependency of the Lean kernel proof.

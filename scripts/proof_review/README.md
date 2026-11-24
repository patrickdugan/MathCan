# Native proof review and finite observation monitors

This tool applies RefutationBench CG-11/CG-12's verified dependency acquisition to ordinary Lean development. It builds selected original modules, checks the transitive axiom set of each reviewed theorem against a per-root policy, and checks optional mathematical interface contracts by elaborating a theorem alias of the explicitly stated type.

Run from a clean, committed repository with its pinned toolchain:

```sh
python scripts/proof_review/review.py --manifest scripts/proof_review/mathcan.json --out /tmp/mathcan-review
```

The manifest is trusted source; its contract strings are Lean expressions. Add modules and fully qualified theorem names, approved axiom lists, optional pinned exact axiom sets, and optional contract types. Graph-enabled modules must be ordinary source files with supported local declaration kinds. A separate instrumentation copy adds an import and a native command, walks elaborated types and values, and reconciles the resulting closure against independently imported original axiom reports. Paths end at explicit axiom declarations or imported summaries. The tool verifies axiom-set agreement, not identity of the instrumented proof term with the original.

Outputs include review.json, review.md, graphs.json, native logs, source/manifest hashes, exact axiom sets, and dependency paths. An unapproved assumption, changed pinned axiom set, unsupported graph, failed contract, missing root or native failure blocks the check. An explicit type contract checks whether the selected proof inhabits the stated type; it does not validate prose, mathematical relevance, or the equivalence of a natural-language advertisement to that type. A strict foundation policy concerns a particular proof, not the falsity or constructive unprovability of its conclusion.

The first manifest includes nine CG-12 originals and nine new constructive lemmas. Classical choice remains explicitly approved for the two original general existence proofs. New lemmas are checked against the narrower choice-free policy.

## Application to agent monitors

MathCan.ConstructiveObservationAudit provides a deterministic list-based observation quotient and authorization classifier. The abstract existence results use surjectivity and classical choice; the executable specializations use an explicit representative function or a list covering the observation image and decidable equality. The classifier returns false for an observation absent from the table. Exact agreement on reachable states is conditional on coverage and fiber compatibility; neither assumption is inferred from finite observations alone.

For Control-Harness or BitAgent, the representative table can be a verified set of public states and the Boolean authorization predicate an explicit policy. The finite monitor can run without a neural classifier. A learned audit controller may prioritize suspicious observations, but cannot override verified authorization decisions. The proof concerns this finite-table abstraction and is not a certification of either deployed application.

## CI
The workflow checks original roots and explicit contracts, asserts the choice-free policy on new lemmas, and performs a negative policy test by excluding Classical.choice for the known original choice-dependent factorization. It also checks that a deliberately invalid type contract fails at native elaboration. No model training is needed for this release gate.

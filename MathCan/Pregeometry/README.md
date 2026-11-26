# Pregeometry: exact decoding and operational witnesses

This folder contains Lean proofs for the observation layer of the PGC program. The state spaces and operations appear explicitly in each definition. Claims about physical geometry require a justified primitive model and a continuum argument.

From the repository root:

```sh
lake build MathCan.Pregeometry
python3 research/pregeometric_identifiability/verify_lean_extension.py
```

The entry point also imports the original four statements in [OperationalIdentifiability.lean](../OperationalIdentifiability.lean). The extension imports `Std` and uses the repository's Lean 4.35.0 toolchain.

## ObservationFactorization.lean

For an observation map `observe : World → Record`, `ObservedClasses observe` identifies worlds whose records agree. The class map embeds injectively into the record type, and its image is exactly the set of reachable records. The principal equivalence is

\[
\bigl[\forall a,b,\ o(a)=o(b)\Rightarrow p(a)=p(b)\bigr]
\quad\Longleftrightarrow\quad
\exists!\,d:\operatorname{ObservedClasses}(o)\to P,\quad
\forall w,\ d([w])=p(w).
\]

The construction lifts `property` through a quotient. Its equivalence and uniqueness results depend on `Quot.sound`; classical representative choice is absent from that construction. Producing a quotient class from a raw record requires a separate computational account.

The total-extension theorem supplies an explicit default value for unreachable records. Its implementation uses classical choice for a representative of each reachable record and classical decidability for reachability. The exact dependencies are printed in the validation log. An example with empty worlds, unit records and empty property values proves fiber constancy while ruling out a total decoder, exposing the condition needed for an unrestricted extension.

## OperationalCounterexamples.lean

The primitive register state is `Fin 4 → Bool`, with a supplied tick count. The diamond update is

\[
F(x_0,x_1,x_2,x_3)=(0,x_0,x_0,x_1\mathbin{\mathrm{XOR}}x_2).
\]

For every initial context, the target equals zero after two updates. The source affects a middle register at the first update, and an independent intervention on that middle register can affect the target at the next update. The defined `EventResponse` relation therefore fails transitivity. Each comparison resets an arbitrary common context at its selected source event; those operation rules form part of the theorem. A separate clamp theorem overwrites the second middle register after one update and recovers the original source response.

The truth-table section uses four queryable outputs of `f(x,z)`, indexed by `2*z+x`. Flipping any entry of an independent table creates dependence. When that entry was unqueried, every observed output stays the same. Consequently, a certificate of independence over all sixteen tables must cover every entry, and any query list carrying such a certificate has length at least four. Repeated queries are allowed in the length theorem.

The explicit all-zero table and the table whose final entry is one agree on the first three queries. Query four separates them. The Lean statements quantify over exact query records; adaptive protocol execution and expected query costs belong to the [companion experiment](https://github.com/MoralityLabAI/SelfModels/tree/a65ffab7ce5a0ce0a6044b37d5f15fc869921fd8/research/pregeometric_observer).

## Verification and scope

[extension_validation.json](../../research/pregeometric_identifiability/extension_validation.json) records source hashes and the axiom inventory for every extension theorem. CI compiles the entry point, then reproduces [extension_axioms.log](../../research/pregeometric_identifiability/extension_axioms.log) exactly. The report distinguishes quotient dependencies and classical choice wherever Lean prints them.

The proofs establish statements about abstract observation maps and declared Boolean systems. The [research synthesis](../../research/pregeometric_identifiability/PGC_NCG_SYNTHESIS.md) records the further requirements for Lorentzian geometry, null boundaries, dimension selection, Einstein variables and Newton's coupling.

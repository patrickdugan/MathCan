# BSAR-04: pinned Lean 4 kernel and axiom audit

Source revision: [`VivienSweetbrier/bsa-r@80c62433`](https://github.com/VivienSweetbrier/bsa-r/tree/80c62433b0eb671175bd8d6169822d3ebd922b60). This follows [BSAR-01](https://github.com/patrickdugan/MathCan/pull/165) and [BSAR-02](https://github.com/patrickdugan/MathCan/pull/168).

## Question

Can the six published BSA-R Lean round files compile independently at the declared Lean 4.35.0 toolchain, and what axioms appear when the compiler executes their embedded `#print axioms` commands?

The original Step 2–7 files contain printed axiom checks and source claims about constructive integer/vector identities, along with conditional inequalities. A successfully kernel-checked statement verifies the typed proposition as written. The separate claims about regularity of every smooth unforced three-dimensional Navier–Stokes solution require analytic definitions, a priori PDE estimates, and proof bridges that are absent from the source-level signatures audited in BSAR-01/02.

## Reproduction

The workflow [`bsar04-native-kernel.yml`](../../.github/workflows/bsar04-native-kernel.yml) checks out the exact BSA-R SHA into `external/bsar`, verifies the source pin, installs the pinned Lean toolchain, and independently executes:

```sh
lean external/bsar/lean/Step2ViscousCooldown.lean
lean external/bsar/lean/Step3ArbitraryDataRound2.lean
lean external/bsar/lean/Step4UltravioletGevreyRound3.lean
lean external/bsar/lean/Step5SpectralVarianceTaoRound4.lean
lean external/bsar/lean/Step6BiotSavartCommutatorRound5.lean
lean external/bsar/lean/Step7VorticityDirectionPdeRound6.lean
```

Each file gets a SHA-256 source record and compiler output, with a global check that rejects `sorryAx` and `Classical.choice` in the printed axiom output. A JSON manifest identifies the exact source and stdout hashes. All outputs are preserved as GitHub Actions artifacts even on failure.

## Limits and follow-ups

The workflow checks upstream source in an isolated CI runner and changes neither project at runtime. The original source does not import MathCan or mathlib; the test uses Lean 4 core. This verifies which theorems compile at the declared toolchain, and whether the emitted axiom audit includes the prohibited names. A broader proof-assurance review should inspect the theorem elaboration environment, the full set of axioms, and all mathematical interpretations of the certified statements.

The high-priority analytic bridge remains a well-typed PDE inequality deriving the `LerayDoublingChain` hypotheses, with a uniform bound on the number of windows as a candidate singular time is approached. A proof of a finite integer chain conditional on its premises does not itself yield such a bound.

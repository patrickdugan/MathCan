# MM-GYM-01: Metamath proof certificates

Status: fixed-prefix local replay and mutation census completed in JavaScript; independent upstream verification is a CI gate, not a completed result. No Lean theorem has been translated, no full set.mm database has been replayed, and no model has been trained.

## Reproduce

Node 20+; no package installation.

```sh
node research/metamath_gym/mm_gym.mjs /tmp/mm-gym
python research/metamath_gym/differential.py /path/to/pinned/mmverify.py /tmp/mm-gym
```

The generated valid.mm contains real uncompressed Metamath statements with a fixed implicational calculus prefix (wi, ax-1, ax-2, ax-mp and floating hypotheses). The separate DV fixture is synthetic and carries no mathematical claim. Candidate proofs can only name the seven frozen labels; they cannot introduce axioms, hypotheses, declarations, or reference earlier generated theorems. The local replay oracle checks stack arity, floating types, instantiated essential hypotheses, distinct-variable constraints, and the exact final statement. It does not parse arbitrary databases, compressed proofs, or includes. It is not a production verifier.

The reference generator constructs A -> A for all ordered binary implication trees with 0..3 internal nodes and leaves ph or ps. Each example masks one label, enumerates the entire candidate action set, and records all valid completions. Train uses 0..1 nodes, development uses 2, and the public depth challenge uses 3. This is a structural generalization smoke test with a shared proof template; it is not a sealed test or a claim of mathematical reasoning. The reference answer may not be the unique valid completion. Never train on oracle.jsonl for the depth challenge.

## Local receipt

```json
{
  "schema": "mm-gym-01-v1",
  "cases": 102,
  "split_counts": {
    "train": 6,
    "dev": 16,
    "depth_challenge": 80
  },
  "reference_steps": 16776,
  "max_stack": 12,
  "mutation_checks": 100656,
  "mutations_accepted": 0,
  "mutations_rejected": 100656,
  "alternative_single_step_proofs": 0,
  "masked_valid_candidates": 102,
  "masked_invalid_candidates": 612,
  "negative_dv_cases": 2,
  "local_assertions": 10,
  "scope": "fixed uncompressed implicational fixture plus separate synthetic DV controls; no set.mm or external verifier run"
}
```

Full single-label mutation census is local. The differential job tests the generated valid proofs and all rejected masked-step candidates, plus both invalid DV cases, against pinned mmverify.py. A crash or timeout fails the job; an explicit Metamath rejection is required. The frozen upstream reference is [mmverify.py at 63a2aa3815cd5bf67892dbfc7f2048cbb177524c](https://github.com/david-a-wheeler/mmverify.py/tree/63a2aa3815cd5bf67892dbfc7f2048cbb177524c). The eventual corpus anchor is [set.mm at 806509385370b29fe8b1723804777ac21b1ce194](https://github.com/metamath/set.mm/tree/806509385370b29fe8b1723804777ac21b1ce194); the pilot does not load it. Upstream [verification policy](https://github.com/metamath/set.mm/blob/806509385370b29fe8b1723804777ac21b1ce194/verifiers.md) describes independently implemented verifiers.

## Foundational acceptance policy

Keep existing LEAN-CHECKED evidence labels. Introduce MM-REPLAYED for a proof checked against a frozen database by an identified verifier, and MM-INDEPENDENT for agreement of at least two independently implemented external verifiers on the same immutable certificate and database. A real cross-formalization additionally requires statement correspondence, dependency/axiom closure, and a review of definitions, types, quantifiers and assumptions. Reject unknown axioms, unproved placeholders and changes to the trusted database. Bind source, theorem statement, dependency closure, proof, verifier binary/source, and configuration to hashes. An arbitrary new $a is not a foundational proof. For high-stakes certificates, target all five upstream verifier implementations where practical. None of these labels should be applied to the local pilot before external checks.

## Next gates and companion repos

- MM-02: parse the pinned upstream database, decompress proof references with dependency order and scope retained, and replay an allowlisted theorem subset using two external verifiers (e.g. C metamath and mmverify.py). Freeze statement and dependency hashes; exercise upstream metamath-test fixtures.
- MM-03 / EvalMath and DataGoblin: dependency-family grouped, chronology-aware splits on real theorems; export proof states and negative actions as JSONL with source hashes. Keep oracle labels and sealed test material out of model prompts. Compare exact-validity, solved-root rate, calls, expanded steps, tokens and wall time against syntax and retrieval baselines. The pilot files are suitable only for loader development.
- MM-04 / LoopedTransformers and BPD: recurrent state carries remaining goal, prefix stack, allowed hypotheses and DV context; route proof repair using BPD components. Match model roots, verifier calls, candidate budget, updates, and wall-time separately. Compare ordinary training, BPD task steering, and rank/norm-matched sham. Evaluate without intervention, with corruption and unseen dependency families; freeze gates before training. Count unique valid proofs, not agreement with a reference label.
- MM-05 / compactification and RH proof length: define cost relative to a frozen axiom set, encoding, and shared lemma library. Report uncompressed label count, compressed bytes, dependency DAG nodes, and expansion cost separately. A verified proof gives an upper bound in that representation; a lower bound in a bounded search or restricted grammar does not establish a ZFC proof-length lower bound. Establish statement correspondence before using a Lean RH proof as a target.
- MM-06 / OntologicalProofs: start with propositional identity, finite set lemmas, then actual ZFC fragments. Record semantic mappings and both dependency closures; no automatic assumption that a Lean kernel check transfers to set.mm.
- MM-07: cross-verifier mutation and parser tests, certificate substitution attacks, and supply-chain pinning. Keep invalid proofs in the adversarial corpus with explicit rejection reasons.

This PR deliberately changes no existing MathCan declarations, proof status, or cross-repository production workflow. The next phase must be registered separately.

## Second external verifier and upstream baseline

The additional C workflow builds [metamath-exe at 580b4bd5ae6f2a0d746398b0033cddccba1b418b](https://github.com/metamath/metamath-exe/tree/580b4bd5ae6f2a0d746398b0033cddccba1b418b), verifies the same positive and negative fixture files, and independently replays the full pinned set.mm with both C and Python. The two jobs must agree; require explicit positive completion and explicit negative errors rather than relying on the C program's exit status. Receipts include SHA-256 for the upstream database, verifier source/binary, positive fixture databases and rejected candidates. This is an upstream baseline, not a translation of the MathCan research corpus. The new workflow's result is pending at source registration.

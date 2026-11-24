# CLN continuation ledger

Source: user-supplied manuscript, "Binary-normal Liouville numbers in the middle-third Cantor set", dated 2026-11-24. Author not supplied. PR #274. Applications discussion is deferred until the mathematical verification phase.

## Gates

| Stage | Scope | State |
| --- | --- | --- |
| CLN-01 | Written generalized theorem; Init arithmetic; exact finite regression oracle | PASS: Lean 12/12, Python 4/4, run 45377255846 |
| CLN-02 | Odd-prime and 2-adic returns; ZMod character orthogonality; exact energy | source submitted, awaiting kernel |
| CLN-03 | Residue fiber cardinality, finite-energy bound, max-mass weighting, normalized envelope | source submitted, awaiting kernel |
| CLN-04 | Summable expected energies, tail averaging, abstract grid interpolation | source submitted, awaiting kernel |
| CLN-05 | Glue CLN02–04 without passing the conclusion as a premise; actual modular orbit collision iff, composite prime-power period assembly, real exponential phase identity | open |
| CLN-06 | Independent digit model, prefix mass and tail independence, probability integration; instantiate the finite grid and countable intersection; Weyl normality | open |
| CLN-07 | Exact Liouville construction, non-atomicity, excluded bases; final theorem and audit | open |
| CLN-08 | Referee pass, source provenance and literature comparison, export proof dependency ledger and reproducible receipts | open |

## Verification rules

- Keep root MathCan on Init. Run the isolated Mathlib subproject on Lean 4.35.0.
- Every new target requires an actual kernel run and exact axiom audit.
- Only propext, Classical.choice, Quot.sound allowed; no sorry, admit, postulates, native-decide shortcuts, or unreviewed theorem-statement weakening.
- Check all premise boundaries; a conditional interface is not the unconditional target.
- Require negative controls: p=2 LTE corner; non-unit base; incorrect modular period; dependent digit prefix/tail counterexample to replacing conditional by marginal min-entropy.
- Distinguish the original supplied argument from CLN extensions. Mathematical validity and historical priority are separate.
- Do not claim the full theorem is verified until the final statement imports the verified proof chain and the exported axioms are audited.

## Tail prompt

Continue the CLN program on MathCan PR #274, branch research/cantor-liouville-prefix-entropy. Read this ledger and the latest PR head, inspect the actual CI job logs, fix the first failing theorem without weakening its statement, and advance to the next open dependency gate. Keep a precise source/target map and update this ledger with commit/run receipts. If CI is queued, develop independent downstream lemmas, but mark them unverified. Continue until the end-to-end original and generalized statements have complete Lean proofs and a clean axiom audit, or explicitly document the exact remaining blocker. Do not switch to applications until the proof and referee audit are complete.

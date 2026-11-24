# CLN continuation ledger

Source: user-supplied manuscript, "Binary-normal Liouville numbers in the middle-third Cantor set", dated 2026-11-24. Author not supplied. PR #274. Applications discussion is deferred until the mathematical verification phase.

## Gates

| Stage | Scope | State |
| --- | --- | --- |
| CLN-01 | Written generalized theorem; Init arithmetic; exact finite regression oracle | PASS: Lean 12/12, Python 4/4, run 45377255846 |
| CLN-02 | Odd-prime and 2-adic returns; ZMod character orthogonality; exact energy | prior job queued then superseded; no kernel receipt yet |
| CLN-03 | Residue fiber cardinality, finite-energy bound, max-mass weighting, normalized envelope | awaiting kernel; run 45379088205 canceled by newer head |
| CLN-04 | Summable expected energies, tail averaging, abstract grid interpolation | source submitted, awaiting kernel |
| CLN-05 | Actual modular orbit collision iff, composite period divisibility, real exponential phase, composed finite second moment | eight source targets submitted; 2,112 finite composite bound checks and four dependent-tail controls passed; kernel pending |
| CLN-06 | Independent digit model, prefix mass and tail independence, probability integration; instantiate the finite grid and countable intersection; Weyl normality | open |
| CLN-07 | Exact Liouville construction, non-atomicity, excluded bases; final theorem and audit | open |
| CLN-08 | Referee pass, source provenance and literature comparison, export proof dependency ledger and reproducible receipts | open |

## CLN-05 checkpoint

CLN05 imports CLN02 and CLN03. Set L=ord_Q(b), z=b^L, M=Q^k,
g=gcd(M,abs(h)), D=M/g, and P=ord_D(b). Every prime dividing D
divides Q and therefore z-1. The return b^P=1 modulo D implies
z^P=1 modulo D. Odd-prime LTE gives v_p(D)<=v_p(z-1)+v_p(P).
For p=2 apply even-exponent LTE to z^(2P)-1, obtaining
v_2(D)<=v_2(z-1)+v_2(z+1)+v_2(P). Consequently
D divides (z-1)(z+1)P, and M divides abs(h)(z-1)(z+1)P.
This is a weaker constant than the prime-specific product but is
independent of k. The formal source includes the actual orbit frequency
collision and the real prefix/tail phase identities.

The next gate must remove the redundant reduced-modulus coprimality and
NeZero premises from the public assembly, derive the positive period
bound from source_power_period_bound, and instantiate orbit_second_moment
with realPhase tail weights and the actual digit-prefix distribution.
Positive Fourier frequencies suffice after deriving conjugation for
negative frequencies; do not omit that step. The CLN06 probability
construction and Weyl theorem remain open. CLN01 remains the only
kernel-certified stage. No complete mathematical theorem is claimed.

Previous head 254c6e46, CI run 45379088205 canceled by newer commits.
Independent Mathlib modules now compile to local .olean files in
dependency order, then run exact axiom allowlist audit (25 Mathlib targets).
The retained Python controls are not asymptotic proofs.

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

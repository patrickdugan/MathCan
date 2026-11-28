# GAL-08: Structural certificates

Full derivations and exact synthetic receipts:
https://github.com/MoralityLabAI/Compactification-Theory/blob/research/gal01-nonperturbative-20261128/Galacticity/GAL08.md

MathCan/GalacticityCertificates.lean contains core-Lean candidates
for certificate-relative observational aliasing, the local Boolean
identities used by affine checking, the mixed difference obstruction,
a small rewrite proof calculus with semantic soundness, cancellation
without subterm expansion, and upfront funding equivalence. The
full black-box adaptive query lower bound, rank-to-affine-square
argument, DAG certificate induction and ANF term-count argument
are paper proofs; the Lean module does not formalize a whole DAG
checker or cryptographic commitment. Hosted CI is configured to check
the module. No native model or cryptographic proof system changed.

# GAL-02: composition and adaptive transcripts

Full mathematical derivation and executable finite-field campaign:
https://github.com/MoralityLabAI/Compactification-Theory/blob/research/gal01-nonperturbative-20261128/Galacticity/GAL02.md

MathCan/GalacticityComposition.lean contains six core-Lean candidates:
three additive-cost inequalities and three finite deterministic adaptive
probe-tree transcript/indistinguishability lemmas. The latter establish
that two worlds agreeing on the actual probe path have identical output,
even when unvisited oracle responses differ. The finite-field
orthogonal-complement argument, rank counting, tensor-product dimension,
and bounded-error expected cost extension remain paper proofs, not
formalized claims in Lean.

GAL-01 initially imported Mathlib, unavailable in this dependency-free
repository. The core-Lean replacement passed the standalone hosted check
at https://github.com/patrickdugan/MathCan/actions/runs/46098619070.

Scope: exact model-relative complexity, with binary slice-local probes
and free arithmetic/storage. No claim about unrestricted RAM algorithms,
actual model performance, or arbitrary serial composition follows.

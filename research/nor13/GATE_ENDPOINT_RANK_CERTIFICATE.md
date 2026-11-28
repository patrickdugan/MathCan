# NOR-13R: endpoint certificates for a gated recurrent task readout

**Research scope, 15 November 2026.** An applied task head may use a frozen trained basin-probability probe \(p(h)\), yet that coordinate can be dispensable for the **ranking** that drives exact proof-template verification. This note gives a finite exact-rational test of its causal role with original model weights frozen.

## The frozen affine-in-gate mechanism

Let \(h\in\mathbb R^{12}\) be the trained RRC-25 GRU state and \(z(h)\) its training-only standardized coordinate vector. A task correction uses scores

\[
s_j(h,g)=b_j(h)+\lambda\bigl(u_j^\top z(h)+g\,v_j^\top z(h)+c_j\bigr),
\qquad g\in[-1,1],\ j\in\{0,\dots,15\}.
\]

The trained NOR-11 probe supplies one specific \(g(h)=2p_{\mathrm{basin}}(h)-1\). With \(h\) and model weights frozen, write \(s_j(g)=a_j+g\,d_j\). Then

\[
s_j(g)=\tfrac{1-g}{2}s_j(-1)+\tfrac{1+g}{2}s_j(+1).
\]

Every pairwise score difference obeys the same convex interpolation identity. If \(s_i(-1)>s_j(-1)\) and \(s_i(+1)>s_j(+1)\), **their strict ordering holds throughout \(g\in[-1,1]\)**. Endpoint ties require checking the deterministic index tie-break.

## Theorem A: finite gate rank certificate

For a ranking of \(n\) classes, suppose the **ordered first \(k\) classes** are identical at both gate endpoints \(g=-1,+1\), and every pair of candidate comparisons needed to establish that order has a strictly positive score gap at both endpoints. Then for every \(g\in[-1,1]\), the first \(k\) ranked candidates remain in exactly the same order.

*Proof.* Each score difference is affine in the gate. Its interior value is a convex combination of its endpoint values, so every needed strict comparison remains positive. Comparisons entirely among classes below rank \(k\) may change. \(\square\)

For NOR-13, \(n=16\) and \(k=4\). The source-native RRC-25 verifier checks candidates in score order and stops at the first public exact candidate accepted, with at most four paid full-template checks. If the ordered top four remain unchanged, the **whole paid verification trace and accepted outcome** are invariant for every gate value, regardless of the basin classifier's AUC.

This makes basin-probe *necessity* a testable mechanistic claim. A probe may predict an attractor accurately, with a nonzero trained task coefficient, yet have no effect on the original reasoning outcome when the relevant candidate comparisons remain invariant.

## Rational arithmetic and numerical scope

The executable companion interprets stored binary64 task weights, hidden coordinates and fixed dev-selected amplitude as **exact rational values**, producing the two endpoint scores and all necessary pairwise comparisons using Python Fraction arithmetic. This computes an exhaustive gate interval certificate, without sampling intermediate gates.

These results certify the ideal affine score function obtained by lifting the frozen binary64 numbers to exact reals. The actual Python evaluator performs finite-precision products and summations. A separate outward rounding-error bound is needed to promote the rational-lift rank guarantee to a complete IEEE-754 implementation-level certificate; near-ties must be marked unresolved. The heldout source-feature hash identifies the model-visible input. The exact original verifier and withheld-future grader are exercised independently.

Twelve distinct late-source cases can share one identical model-visible feature tensor, so all geometric and rank stability statistics report **unique model inputs** alongside raw synthetic case counts.

## The Nat-weight formal kernel

The [Lean module](../../MathCan/NOR13GateOrder.lean) formalizes the finite-denominator version of endpoint interpolation. Suppose the endpoint scores are nonnegative integers and \(g=-1+2t/N\) for \(0\le t\le N\). The unnormalized interpolated score is

\[
\widetilde s_j(t)=(N-t)s_j(-1)+t\,s_j(+1).
\]

The kernel checks pairwise order preservation at any finite interpolation step, order preservation simultaneously across all candidate pairs, and a fixed top-winner witness. A strict order also survives when one endpoint has a strict gap and its interpolation weight is positive. The proof needs elementary Nat arithmetic; the real affine extension and whole ranking transfer are written proofs.

This file is not a formal proof about the full trained GRU, Python float semantics, nor actual model correctness.

## Application to recurrent interpretability

The observable questions are how many **distinct** model inputs have a gate-invariant top-four verification list, how many yield a change in accepted proof templates after gate ablation or substitution, and whether those changes improve verified task outcomes relative to parameter-matched controls.

NOR-12's first held-out test scored 44/72 future-correct with its fitted basin scalar, and still scored 44/72 after zeroing, shuffling or permuting that coordinate. The current independent interaction-gated campaign trains separate task slopes for the two basin modes with matched random-gate, shuffled-probe and constant-gate controls. Endpoint certificates can expose gate-insensitive native task decisions even when weaker geometric probes suggest nontrivial hidden dynamics.

# NOR-16S: a conditional zero-false-accept public proof certificate

Companion to NOR-16 in MoralityLabAI/Compactification-Theory, research/nor16_public_query_consensus.

The synthetic RRC-25 verifier has a finite set of sixteen candidate programs. Let \(A\) be those that pass both complete degree-192 public demonstrations. Every \(p\in A\) can be simulated on the public degree-256 query **input** to yield a hypothetical output \(Y_p\).

A proposed future output \(y\) has a complete public certificate if

\[
\forall p\in A,\quad Y_p=y.
\]

When the planted generator belongs to the enumerated candidate family and the public checker is exact, the actual generating program belongs to \(A\). It follows that its true future equals \(y\). This gives a deductive soundness condition for an **abstaining verifier**, subject to the explicit candidate-family membership assumption.

The kernel-proven [MathCan/NOR16PublicOutputCertificate.lean](../../MathCan/NOR16PublicOutputCertificate.lean) establishes soundness from accepted true-program membership, the special case of a unique accepted candidate, and the impossibility of issuing a unanimous certificate if two accepted candidate programs predict different outputs. Unlike a learned confidence threshold, full-output unanimity is a Boolean proof obligation. Proving that it holds requires exact acceptance checks for all sixteen templates and exact public-query candidate continuations.

The first NOR-16 experiment found 52/192 late_source public inputs satisfying complete predicted-output unanimity. The corresponding accepted predictions were all correct and incurred zero false accepts. The other 140 have concrete accepted-program pairs with divergent hypothetical outputs. The source-controlled empirical JSON pins these facts; Lean verifies the generic soundness and obstruction implications without importing empirical floating-point data.

This certificate proves soundness **only within the declared synthetic candidate family**. An incomplete template universe, incorrect header decoder, altered source generator, or unsound public checker can invalidate generator membership. A policy that must abstain on 140/192 cases also has limited coverage. Any wider reliability claim requires new source-family stress tests and an explicit computational budget ledger.

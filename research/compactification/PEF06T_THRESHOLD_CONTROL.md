# PEF-06T: threshold-only and nonlinear coalition mechanisms

The three-paper PEF-06 campaign studies historical input coalitions.
A pair-only class change can arise without a nonadditive logit map.

For binary inputs x,y, define additive logits z(x,y)=x+y.
The class indicator 1[z>=2] is false at the zero source and at
both single-bit interventions, and true after both bits flip.
Its four-corner logit increment is nevertheless exactly zero:

    z(1,1)-z(1,0)-z(0,1)+z(0,0)=2-1-1+0=0.

The nonlinear AND score z(x,y)=xy also gives a pair-only class
change, but its logit four-corner increment is one.

MathCan/CoalitionThreshold.lean proves the generic additive
four-corner equality and both complete finite witness tables.
This distinguishes threshold-only class synergy from genuinely
nonadditive changes in the continuous logit representation.

The frozen PEF-06T companion compares the actual pair-flip
task-class prediction with a finite additive surrogate

    z_add(x^ij)=z(x^i)+z(x^j)-z(x)

on the same historical inputs. If the additive surrogate predicts
the actual class, a threshold-only account is compatible with
the observation. A disagreement implies a nonzero four-corner
logit difference on that specific quartet, without identifying
a particular circuit or proving a model computes the XOR-AND latch.

The companion uses all 12 original PEF-05 checkpoint SHA256s, and
records the trained h8 head separately from its unsupervised
h10(01) continuation. The source family is reused from the
earlier registered negative study and the results are posthoc.

Relevant sources:

- OpenAI/math #119, Sharp binary-information contraction.
- OpenAI/math #127, Average sensitivity of polynomial thresholds.
- OpenAI/math #132, Superquadratic block versus single sensitivity.
- Compactification-Theory PEF-06 PR #146.
- LoopedTransformers PEF-06 PR #64.

The broad preprint claims are not imported as assumptions.

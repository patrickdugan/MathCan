# DCF-13 decision compactification: formal core

Companion to [Compactification-Theory DCF-13/13D](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/dcf01-dense-compute-frontier-20261125/research/dcf13_decision_compactification).
[`MathCan/DCFDecision.lean`](../../MathCan/DCFDecision.lean) kernel-checks, over integers with `Init` only:

| Theorem | Statement | Used by |
|---|---|---|
| `signedMass_product`, `mass_product` | parity-signed and total masses of independent components multiply, so `P(parity=1) = (1 - s_A s_B)/2` | query-directed component inference (DCF-13A/C) |
| `act_optimal` | with reward +1/-4/0 the threshold policy (act iff the answer has at least 4/5 of the mass) is optimal among answer 1, answer 0 and abstain, and never negative | every DCF-13 to DCF-16 decision |
| `interval_certificate_sound`, `certified_action_nonnegative` | `L1 <= N1`, `N0 <= U0`, `4 U0 <= L1` imply `4 N0 <= N1` | DCF-13B pointwise bounds, DCF-13D credal decisions |
| `bern_nonneg`, `bernstein_certificate_sound` | nonnegative Bernstein-form coefficients give a nonnegative value at every rational `w = a/d` in `[0,1]` | DCF-13D shared-weight credal certificate |

`#print axioms` for the four headline theorems lists only `propext`, `Quot.sound` and (for `act_optimal`, `bernstein_certificate_sound`) `Classical.choice`.

Not formalized: the extension of `bernstein_certificate_sound` from rational to real `w` (density and continuity), the de Casteljau subdivision step, floating-point rounding in the Python implementation, and the exact Bayesian-model-averaging integral `∫ w^i (1-w)^(m-i) dw = i!(m-i)!/(m+1)!`.

Check: `lake env lean MathCan/DCFDecision.lean`.

# RH-01: Analytic window and proof-dependency mathematics

**Research status:** conditional lemmas and finite arithmetic certificates
derived from an externally published claimed proof. The ultimate RH/GRH
result is subject to ongoing independent mathematical examination.

Original upstream Lean repository:
https://github.com/leanprover-community/riemann-hypothesis
pinned to commit f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3.

## What we are trying to settle

The analytic half-plane exclusion uses a Landau window lemma:
a smoothed von Mangoldt sum must have an exponent approaching 1/2.
The source proof of core_gm supplies a bound

    Gm(x) <= x^(1/2 + (eD + eL + 7)*epsilon).

The error exponent is assembled from character balance and size-window
inequalities in the original Lean proof. The upstream compiled proof
terms identify ch_core, ch_top, charsA, gmA_eq, sigA_le and hostFactsS.

Within ch_core, the CharacterBalanceMoves.core lemma feeds the
size-bound proposition; the latter calls SZ.T1, SZ.T2, SZ.T3, SZ.T4
with coefficients 2, 2, 4, 2 in the normalized error budget.
Those conditional calculations are documented in CHCORE_MATH_REVIEW.md.

The source's SizeWindows predicate has 16 scalar conditions. It gives
n^2 >= x for the cardinality n of an auxiliary finite group.
The family-level SizesAt predicate imposes

    x^(2+31*epsilon/4) <= n <= x^(2+33*epsilon/4)

when delta=epsilon/4. This is a much stronger size requirement.
An exact numerical certificate checks that the scalar inequalities
are jointly feasible for two epsilon values. This demonstrates
finite numerical compatibility of selected necessary hypotheses.

The original smallCosts proof uses an exponentially large b and
exponentially small theta, with positive f. This costs substantial
scale in the other inequalities, making the simultaneous admissibility
proof a primary mathematical object for further study.

## Highest-value upstream interfaces

- SizesAt and PlacesAt: finite group, sampling depth and character-set sizes.
- adm5: uniform smoothed character-sum control over y >= X'/3.
- adm6: specified nontrivial character sums and logarithmic derivative estimates.
- adm7: existence of weights, positive eta and TOPineq.
- proposition_eleven_two_at_scale and proposition_eleven_two_along_family:
  transport those hypotheses into the required pointwise prime-sum estimate.

The first two constraints are modeled by exact finite arithmetic.
The analytic and geometric witness constructions remain unverified
by our independent MathCan development.

## Formal-math assets and evidence

- MathCan/RHWindowExponents.lean: Init-only proof of log-scale arithmetic
  certificates for epsilon=1/64 and 1/128. This is a separate theorem
  about finite integers, not an import of the original Mathlib claim.
- rh_window_feasibility.py and rh_joint_scalar_envelope.py: exact
  fraction and dyadic checks, with nearby failing controls.
- chcore_compiled_direct_refs.json and compiled_analytic_direct_refs.json:
  receipts obtained from the original published Lean compiled artifacts.
  Source and cache pins were verified in the originating EvalMath CI.

EvalMath PR #60 retains the proof-term graph extraction and scored
reconstruction tasks: https://github.com/MoralityLabAI/EvalMath/pull/60

## Verification boundaries

1. Direct source callsite evidence is labeled source-only.
2. Published Lean cache references identify constants occurring inside
   proof expressions. They are not proof minimization or a new proof.
3. MathCan native Lean certificates are checked against Lean 4.35 Init.
4. Exact-fraction scalar examples are finite checks. The logarithmic
   and exponential comparisons used as sufficient bounds are cited
   mathematical facts rather than separate Lean formalizations here.
5. Global RH and the complete family/geometric construction are outside
   the independent results currently established in MathCan.

## Next formal work

Inspect the consistency and eventual quantifiers of the full family
hypotheses, especially the interaction of high b and low theta with
the upper-bound constraints on aE and Err. Formalize the exponent
identities that propagate through windows and smallCosts in a Lean
library with matching proof obligations. Keep original source pins.

## Native Lean error-budget lemmas

The `MathCan/RHWindowExponents.lean` module additionally proves two conditional Nat arithmetic lemmas: aggregation of four upper error coefficients 2+2+4+2=10, and the final correction coefficient 4+22=26 when the smaller term is bounded by the main term. Their inputs remain explicit, so these do not replace the original real-variable analytic hypotheses.

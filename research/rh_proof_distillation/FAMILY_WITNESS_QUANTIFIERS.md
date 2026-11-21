# RHD-02: Quantifier audit of the claimed RH family construction

Pinned original source: [ZetaZeroFreeRegion.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src/Formalism/SharpRestriction/GlobalSchurBounds/ZetaZeroFreeRegion.lean), blob \`7746e5a5affe67117d4ba907dbcd2788f539db6e\`. The [family-to-pointwise theorem](https://github.com/leanprover-community/riemann-hypothesis/blob/f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3/src/Formalism/SharpRestriction/GlobalSchurBounds/RamificationTwoAndConjugationAtQAndD.lean#L933) comes from blob \`1c1495ef81c77fa96f3c1a70106c1da9e24c0c5d\`.

## Actual quantifier structure

The published \`AllLargeC\` condition fixes \(\varepsilon\), then requires a **single positive constant** \(c\) and a threshold \(x_0\) such that the analytic statement holds for every \(x\ge x_0\) and every family index at that scale. The \`adm5\` and \`adm6\` inputs of \`proposition_eleven_two_along_family\` have this form. Constants can depend on the chosen \(\varepsilon\), but are uniform in scale and family index.

The source's \`SizesFe\` supplies eventual \`SizesAt\` and \`PlacesAt\` bounds for all indices. The \`TOPF\` predicate uses \`AllLargeAt\`: it fixes a coefficient \(C\), and at every sufficiently large \(x\) there exists *some* index satisfying \`adm7\`. The chosen index may vary with \(x\).

Together these justify the eventual shared-index step of the family-to-pointwise proof. In [MathCan/RHFamilyWitnesses.lean](../../MathCan/RHFamilyWitnesses.lean), \`synchronized_family_witnesses\` formalizes exactly that logical reduction using Nat scales and dependent index types. It takes the analytic conditions as explicit assumptions.

## Nonvacuity and constant quantification

An empty index family satisfies \`EventuallyAll\` vacuously. \`TOPF\` supplies an eventual existential condition, so the *complete* premise implies every sufficiently large index type is inhabited. \`eventual_selected_index_forces_nonempty\` formalizes this consequence; the empty-family lemmas give explicit positive and negative examples.

\`AllLargeC\` is stronger than scale-wise existence of a suitable constant. The MathCan counterexample uses the elementary relation \(n\le C\): each \(n\) permits \(C=n\), while a single finite \(C\) cannot work for every \(n\). A separate alternating-index example shows that the \`TOPF\` witness may depend on scale.

## Stronger cardinality floors

Write \(L=\log_2 x\) and \(q=\varepsilon L\), assuming those quantities and the relevant cardinality logarithms are integers. The upstream \`SizesAt\` lower bound with \(\delta=\varepsilon/4\) gives

\[
4\log_2 n \ge 8L+31q.
\]

The \`PlacesAt\` lower bounds yield

\[
8\log_2 n_T+q+8\ge 8\log_2 n,
\qquad
\log_2 n_{T2}+q\ge\log_2 n.
\]

Combining them,

\[
8\log_2 n_T+8\ge16L+61q,
\qquad
4\log_2 n_{T2}\ge8L+27q.
\]

These are independent, exact arithmetic consequences encoded in \`character_subsets_inherit_quadratic_scale\`. They show that the source's eventual character-set witnesses must be large at the same scales as the auxiliary group.

## Mathematical scope

The Lean theorems concern logic and integer exponent inequalities under supplied premises. They do not construct \`FamP\`, \`D7\`, \`Scale\`, \`adm5\`, \`adm6\`, \`adm7\`, \`Gc\`, \`GivenAll\`, or \`TOPineq\`. Consequently, this work verifies conditional steps of the proposed architecture without independently establishing RH.

The next mathematical target is the compatible joint production of \`adm5\`, \`adm6\`, \`SizesFe\`, and \`TOPF\` from the published geometry and arithmetic constructions. Their uniformity and existential quantifiers need careful source and proof-term tracking.

## Constants quantified in the correct order

The additional native Lean theorem `uniform_character_constants_on_selected_index`
encodes the two `AllLargeC` constants directly. For a fixed epsilon, each
positive coefficient is chosen **before** the eventual threshold, scale
and family index. It then specializes both estimates to the index
chosen by `AllLargeAt`, whose own positive coefficient is fixed.

This proof is a literal logical statement with Nat as the scale
parameter; the upstream Real-valued `adm5`, `adm6`, `adm7`
hypotheses remain explicit and unconstructed.

## Coefficient scope across epsilon

The original `TOPF Fm ε0 C` fixes `C` before its universal epsilon quantifier. The original `AllLargeC` chooses the `adm5`/`adm6` constants after epsilon but before x and the family index. `coefficient_fixed_across_epsilon` is an independent Lean 4.35/Init theorem for these nested quantifier scopes. It retains a single positive `C` across all epsilon values while allowing positive `c5` and `c6` to depend on epsilon. The dependent index type may vary with both epsilon and scale.

This is a proof of logical synchronization, conditional on all the original-shaped premises. It supplies no analytic `adm5`/`adm6`, geometric `adm7`, or eventual family construction.

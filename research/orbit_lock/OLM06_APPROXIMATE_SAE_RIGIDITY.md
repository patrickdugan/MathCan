# OLM-06: Sparse-autoencoder precision, one-swap aliases, and the 13-state rigidity threshold

**November 15, 2026.** Companion to [OLM-05](OLM05_SPARSE_GEOMETRY_RIGIDITY.md) and [SMC-06](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/smc01-synchronized-mixing-20261115/research/synchronized_mixing_v1). The motivational source pair remains OpenAI Mathematics [#131](https://github.com/openai/math/blob/main/lean/docs/131.md), graph-switch mixing, and [#238](https://github.com/openai/math/blob/main/lean/docs/238.md), permutation mixing. No proof or mixing bound from either source is imported here.

**Status:** elementary real-analysis and information-theoretic lemmas with self-contained proofs, plus *computer-assisted exhaustive finite classifications*. The synthetic SAE measurements test the resulting predictions; they are not evidence of pretrained transformer representations. Priority relative to the literature has not been established.

## 1. Precise object and epistemic contract

There are 15 true matching-edge channels, with 15 possible three-hot perfect-matchings of the six vertices. A 40-dimensional observed activation is a noisy, dense linear mixture of an unknown 15-atom dictionary. A trained 40→15→40 ReLU sparse autoencoder produces 15 nonnegative approximate feature scores. Neither the feature-to-edge permutation nor the relevant vertex-gauge group is passed to the geometry estimator. The **matching/complete-graph hypothesis family and three-hot cardinality remain explicit priors**. These are important restrictions of the experiment.

For each observed matching-state episode, take the top three mean SAE activation scores. A structural estimator either finds a unique global six-star cover, searches a predeclared budget of one active↔inactive channel swap across the 12 observed state rows, or abstains. A valid cover establishes that the **observed masks** form an anonymous K6 matching geometry. Whether they reproduce the **planted geometry** is a separate fidelity question.

## 2. An exact activation-margin stability lemma

Let a∈R^F, with entries ranked a_(1)≥...≥a_(F), and let T_k(a) be its indices of k largest entries under a fixed tie rule. If

\[
\gamma=a_{(k)}-a_{(k+1)}>0,
\]

then for every perturbation e with ||e||_∞ < γ/2, T_k(a+e)=T_k(a). Indeed every selected-minus-unselected score difference changes by at most 2||e||_∞ and its original value is at least γ. For a matrix of state episodes, take the minimum γ across rows. A fixed combinatorial geometry or one-swap search that uses **only** these top-k masks returns the same result under this bound, including the same abstention reason if search order and budgets are fixed.

### Matching-score margin

Suppose a learned geometry admits k-hot perfect matching supports M. The score s(M)=Σ_{j∈M}a_j is maximized uniquely at M*, ahead of the second-best candidate by δ>0. Under ||e||_∞<δ/(2k), s(M*;a+e) still exceeds every other matching score. The difference between any two k-term sums changes by at most 2k||e||_∞. This *certifies local decision stability*, not whether M* equals the actual heldout matching. In SMC-06 a failing SAE can be confidently wrong.

The independent [exact rational margin checker](sae_precision.py) evaluates the inequalities without reliance on floating-point matrix decomposition. It can read archived decimal SAE scores as exact rational strings. Neural activations themselves remain finite-precision measurements.

## 3. A silent-atom identifiability barrier

Consider a latent sparse vector z, decoder D=[d_1,...,d_F], and observed activation y=Dz+ξ, with noise ξ whose law is independent of D. Assume an atom j is **never active in the training population**, i.e. z_j=0 almost surely. Replacing d_j by any other vector d'_j leaves the entire training-data law unchanged, for every sample size N.

**Proof.** For every train latent input, Dz=Σ_{i≠j}d_i z_i. The value of d_j drops out identically; hence the conditional and marginal observation laws are identical under the replacement. No estimator of d_j from these observations can distinguish a pair of priors assigning equal mass to two different values, so its worst-case exact identification probability is at most 1/2. For Q equiprobable alternatives the upper bound is 1/Q. QED.

This resolves a subtle issue from OLM-05: a completely silent **already-identified feature channel** may be placed combinatorially by the global star-cover constraints, even though a newly trained SAE **cannot infer that feature's continuous decoder direction** from matching-only data that never activate it. SMC-06 therefore includes independent singleton and pair exposures for dictionary training. They carry **no matching-class labels**. An ablation removes those exposures and exposes the resulting loss of support-level identifiability.

## 4. Sharp finite one-swap aliasing for twelve matching states

Let B_H be the twelve-row three-hot incidence matrix obtained by omitting three of the 15 K6 matching rows H⊂Ω. An *elementary substitution* replaces one active channel with one inactive channel in exactly one observed row, keeping that row's Hamming weight three.

**Theorem OLM-06A (exhaustive finite classification).** Across all 455 omitted triples, there are **exactly 180** substitution events for which the corrupted twelve-row matrix remains a valid anonymous K6 matching codebook under a *different* six-star geometry. Each event belongs to a distinct omitted triple: **180** deletion triples have one such alias and **275** have none. Every alias comes from an eleven-row subset with the two alternative star covers classified in OLM-05. All **180** alternate geometries induce a matching-label mapping on the twelve observed states that is compatible with a common S6 vertex relabeling.

**Finite verification.** Iterate all C(15,3)=455 omitted triples and each of the twelve choices of a state to alter, leaving 5,460 eleven-state subcohorts. Compute up to two exact six-star covers of each eleven-row cohort. For each cover, generate all 15 three-hot matching rows under that geometry and retain replacements at Hamming distance exactly two from the original removed row, absent from the other eleven. Verify that the resulting twelve-row codebook has exactly one cover, then exhaustively test all 720 vertex relabelings against the original twelve labels. The integer oracle [alias_catalog.py](alias_catalog.py) reproduces these counts and exports every alias and its swapped channel pair. The 180 events correspond to the 45 ambiguous four-omission patterns of OLM-05, each with four choices of the row restored before substitution.

This is a *computer-assisted finite theorem*, not a closed-form classification proof for arbitrary graph sizes. The fully self-contained correctness of enumeration follows from exhaustive finite combination/backtracking loops, with explicit shape and row constraints.

**Consequence.** A twelve-row global-star cover, even when unique, can be a mathematically valid **incorrect** geometry after one adversarial feature substitution. A vertex-equivariant matching-label calibration restricted to those same twelve observed classes can remain consistent with that alias. Therefore a structurally valid output from an SAE must be interpreted as a certificate of its *observed codebook*. Claims about the planted model require an independent source-fidelity check or additional information.

A concrete witness in canonical feature order: omit matching classes (0,1,5), replace feature index 12 by index 0 in training class 12. Both the clean and altered twelve-row matrices have unique global K6 star covers, and the covers differ. The exact regression suite pins this witness.

## 5. A sharp thirteenth-state detection threshold

**Theorem OLM-06B (single-swap detection for thirteen classes).** Observe any thirteen **distinct true K6 matching states** as anonymous three-hot feature rows. Replacing one active feature in any single row with one inactive feature always produces a matrix that fails the K6 matching-codebook constraints. Thus a global cover with all thirteen valid rows detects any single elementary substitution, even without knowing the feature-to-edge permutation.

**Proof.** Remove the corrupted row. The remaining twelve uncorrupted rows uniquely determine the vertex stars and feature-edge incidence up to gauge by OLM-05's 455-case exact finite rigidity theorem. In that recovered geometry the two untouched edges in the corrupted row are disjoint and already cover four vertices. They have a **unique** complementary edge between the remaining two vertices. The original removed feature is precisely that edge; replacing it with any other channel cannot complete a perfect matching. No alternative geometry can fit the twelve unaltered rows because their global cover is unique. Hence the thirteen-row corrupted matrix has no valid cover. QED relative to the established finite OLM-05 classification.

At twelve rows, the 180 aliases above prove that this worst-case detection guarantee is false. Hence **thirteen distinct observed states is a sharp threshold for arbitrary one-substitution detection** on the K6 perfect-matching family. The theorem is about error **detection**. Unique *repair* and correctness of approximate, systematically mixed SAE features are additional claims and remain separately tested.

For K6, the exact finite enumerator confirms all C(15,2)=105 uncorrupted thirteen-row cohorts have a unique star cover (60 with six candidate stars, 45 with thirteen).

## 6. What the actual trained SAE experiment measures

The applied model in SMC-06 is a real gradient-trained sparse autoencoder on **synthetic dense residual mixtures**. Training uses 16,000 input vectors of dimension 40, a width-15 ReLU code and linear decoder, 1,215 parameters, L1 activation penalty, Adam 0.003 and 9,000 optimization steps per seed. The generator includes unlabeled singleton atom probes (70%), independent pairs (24%) and triple-matching observations from only twelve allowed matching classes (6%). Matching-state evaluation averages 64 noisy activation observations before top-three extraction; the three heldout triple classes are never presented as complete matching training patterns.

Ten registered seeds 101–110 produce **six structurally certified** feature geometries, with at most one whole-row swap repair, and four abstentions. Fixture-side checks find the planted vertex incidence up to relabeling in all six accepted seeds. Five accepted seeds decode all three unseen matching classes correctly, reaching the 5/6 heldout Bayes balanced accuracy for each of three hidden frame seeds; the remaining accepted seed misdecodes one class and attains 13/18. The mean heldout accuracy **conditional on accepted geometry** is 22/27 (~81.48%). This score is conditional and abstentions remain separately reported.

Without independent singleton/pair anchors, both tested initializations abstained. Equal-dimensional PCA absolute-coordinate and untrained random-ReLU controls each abstained on three tested seeds, even though PCA attained low dense reconstruction error. These are bounded synthetic checks; no claims about pretrained transformer SAEs, generalized support recovery, or discovering arbitrary group families follow.

The combined result separates three statistical obligations:

* learn the continuous sparse dictionary from sufficiently rich unsupervised exposures;
* infer the discrete incidence geometry from a restricted set of approximate coactivation observations, with safe abstention;
* recover a gauge-compatible frame and test independent heldout states, including an explicit provision for one-swap aliasing.

The finite codebook and margin theorems describe what these stages can certify. Empirical SAE optimization is measured separately.
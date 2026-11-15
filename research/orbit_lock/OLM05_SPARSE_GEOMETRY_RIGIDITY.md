# OLM-05: Rigidity of anonymous matching features under deleted states

November 15, 2026. Continues [OLM-04](OLM04_TRANSPORT_IDENTIFICATION.md). The research source pair remains OpenAI Mathematics [#131, degree-preserving switch-chain mixing](https://github.com/openai/math/blob/main/lean/docs/131.md) and [#238, full-permutation mixing](https://github.com/openai/math/blob/main/lean/docs/238.md). The finite matching constructions below are separately specified. These are original deductions for this research campaign; priority relative to existing mathematical literature has not been established. The two finite classifications are *computer-assisted, exhaustive integer certificates*, not Lean-kernel proofs.

## 1. Anonymous coactivation geometry

Let E be the 15 edges of K6 and Ω the 15 perfect matchings on six vertices. For M∈Ω, its feature row x(M) is the 15-bit vector with exactly three ones, corresponding to its matching edges. An unknown permutation of the 15 feature channels hides their endpoint labels. The learner receives a set D of distinct anonymous three-hot rows and is promised only the six-vertex perfect-matching model.

Define the **conflict graph** C_D on feature channels: distinct channels are adjacent when no observed row coactivates both. Each real vertex of K6 has a *star* of five incident edges, so its five channels form a clique of C_D. Deleting matching observations creates extra conflict edges. The set of all five-cliques need not consist only of vertex stars.

A **six-star cover** is a set of six five-cliques such that any two meet in exactly one channel, and each of the 15 channels belongs to exactly two cliques. Interpret the cliques as six abstract vertices. Every channel is then the edge connecting its two cliques. Because each clique pair meets in one distinct channel, the reconstructed incidence graph is K6.

### OLM-05A: Uniqueness from a global star cover

**Theorem.** If C_D has exactly one six-star cover, the K6 feature-to-edge correspondence is uniquely determined up to relabeling the six reconstructed vertices.

**Proof.** Every putative K6 realization of the anonymous data supplies its six real vertex stars. Edges incident to the same vertex cannot occur together in a perfect matching, so each star is a five-clique of C_D. Two stars meet in their shared edge; each edge belongs to two stars. Thus any valid realization induces a six-star cover. Uniqueness forces this cover, and each channel's two incident stars determine its endpoints. Naming the six stars differently is precisely vertex-gauge freedom. QED.

Each three-hot observed row becomes a perfect matching of this incidence graph, because a coactive pair cannot share any chosen star; three pairwise disjoint edges cover all six abstract vertices.

## 2. Exhaustive K6 partial-observation rigidity

**Theorem B (computer-certified, 455 cases).** Every choice of 12 observed perfect matchings out of the 15 gives exactly one six-star cover, even if three missing matchings make a feature completely silent. The exact integer audit groups the three omitted matchings by their pairwise shared-edge counts:

| Pairwise shared edges among three omissions | Number of omissions | Candidate five-cliques | Valid six-star covers |
|---|---:|---:|---:|
| (0,0,0) | 80 | 6 | 1 |
| (0,0,1) | 180 | 13 | 1 |
| (0,1,1) | 180 | 24 | 1 |
| (1,1,1) | 15 | 47 | 1 |

A naive "exactly six five-cliques" criterion would certify only 80 cases. The global incidence constraints select the unique legitimate cover for the other 375 cases.

**Theorem C (computer-certified, 1,365 cases).** With 11 observed matchings (four omitted), exactly 1,320 omission sets have one cover, while 45 have exactly two covers. The ambiguous 45 are precisely the four-matchings omissions whose *shared-edge graph* is two disjoint edges: two disjoint pairs of omitted matchings each share an edge, and all four cross-pairs are edge-disjoint. For these cases the data admit two compatible latent K6 geometries and the estimator must abstain.

**Finite proof protocol.** Recursively enumerate every perfect matching of six vertices by pairing the first remaining vertex. For each omitted set compute all channel cooccurrences and all C(15,5)=3,003 five-clique candidates, then backtrack over six distinct candidate cliques, requiring exactly one feature in each pairwise intersection and feature incidence at most two. A complete cover must use every feature exactly twice. Stop after two solutions when testing uniqueness. The fully explicit [exact oracle](latent_stars.py) executes all 455+1,365 subsets and checks each claimed category; [tests](../../tests/test_latent_stars.py) independently require the counts, covariance identities and noise bounds. This is an exhaustive finite mathematical certificate. A nonenumerative classification of these particular holdout patterns remains open.

## 3. Deriving the global symmetry family

**Theorem D.** The automorphism group of the complete incidence/conflict graph L(K6) is S6.

**Proof.** In L(K6), a clique of size at least four consists of edges of K6 with a common endpoint. Three distinct pairwise-intersecting edges either share an endpoint or form a triangle; no fourth distinct edge meets all sides of the triangle. Hence each size-five maximal clique is one of the six K6 vertex stars. Any automorphism permutes these six stars. Each original edge is their unique pairwise intersection, so the images of all edges are determined by that star permutation. Every permutation of six K6 vertices induces such an automorphism, and the induced action is faithful. Thus Aut(L(K6))≅S6. QED.

In the SMC-05 application, the learner first reconstructs these six abstract stars from observed sparse features, then uses the resulting S6 candidate action for frame calibration. The six-vertex/perfect-matching model class remains an explicit prior; the experiment does not discover that class from arbitrary model activations.

## 4. Binomial noise certificate

Assume each of the 12 latent matching states has R independent repeated 15-channel binary readings, with true-positive rate p>1/2 for active features and false-positive rate q<1/2 for inactive features. Majority vote is strict: output one when more than R/2 readings are active. Put

\[
\beta_-=\Pr(\operatorname{Bin}(R,p)\le R/2),\qquad
\beta_+=\Pr(\operatorname{Bin}(R,q)>R/2).
\]

Across 12 three-hot states there are 36 one-bits and 144 zero-bits. Under independent sensor errors, the exact probability that **all** 180 bits are recovered correctly is

\[
\boxed{P_{\mathrm{all}}=(1-\beta_-)^{36}(1-\beta_+)^{144}.}
\]

Theorem B guarantees that accurate bit recovery implies unique geometry recovery. Hence its success probability is at least P_all. An exact union bound on bit error is \(36\beta_-+144\beta_+\). For a general threshold (p+q)/2, Hoeffding gives the looser bound \(180\exp[-R(p-q)^2/2]\).

Exact binomial arithmetic (floating values rounded for display):

| p | q | Repeats/state | Geometry-success lower bound |
|---:|---:|---:|---:|
| 0.90 | 0.10 | 16 | 0.99694379 |
| 0.75 | 0.25 | 40 | 0.95523814 |
| 0.75 | 0.25 | 64 | 0.99881592 |

The inputs are grouped by recurring state episode. Recovering which noisy samples correspond to the same state is another inference task.

## 5. Covariance and the sampling-law trap

Under a **uniform matching** on 2k vertices, each edge indicator X_e has mean \(1/(2k-1)\). For distinct edges e and f:

\[
\operatorname{Cov}(X_e,X_f)=
\begin{cases}
-\frac1{(2k-1)^2},&e,f\text{ share a vertex},\\
\frac2{(2k-1)^2(2k-3)},&e,f\text{ are disjoint}.
\end{cases}
\]

**Proof.** Incident edges never cooccur. Two disjoint edges cooccur with probability \(1/[(2k-1)(2k-3)]\). Subtract the product of their marginal probabilities. QED.

Under conditionally independent binary sensor noise \(Y_e\) with \(\mathbb E[Y_e\mid X_e]=q+(p-q)X_e\),

\[
\operatorname{Cov}(Y_e,Y_f)=(p-q)^2\operatorname{Cov}(X_e,X_f)
\]

for distinct edges. Thus covariance **sign** recovers the true edge-incidence relation from full uniform-state data when p≠q. The 12-class selection violates the uniform full-orbit assumption. Some disjoint true edges never coactivate in that restricted cohort, so naive sign/absence tests can invent incidence. The global six-star cover corrects that ambiguity.

## Evidence and limitations

[MathCan oracle](latent_stars.py) checks the full 1,820-subset classification with exact integers, noise probabilities with Fraction, and covariance directly over matching enumerations for k=2,3,4. [SMC-05](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc01-synchronized-mixing-20261115/research/synchronized_mixing_v1/SMC05_ANONYMOUS_FEATURE_GEOMETRY.md) tests end-to-end hidden-frame identification after the geometry is reconstructed from **only training-state activations**, including a previously unseen matching class with a completely silent edge feature during training. No pretrained transformer, trained SAE, broad literature-priority claim, or Lean-kernel proof is asserted.

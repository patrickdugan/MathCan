# SelfModels continuity mathematics, v0.1

**Status:** standalone mathematical statements, proof arguments, and exact finite Python tests. No Lean kernel check, training run, natural-language agent evaluation, SAE recovery, or GPU result is claimed. All assumptions below are part of each result.

## Model

An agent consists of a verified ordered event history `E`, a canonical projection `S(E)`, a language-model checkpoint `theta`, and a versioned external persona `phi`. The canonical event reducer is assumed to use only authorized records and exact typed transition rules. The reference implementation covers a finite *positive support DAG* and model-attributed interpretations. It is neither a complete AGM revision operator nor an authenticated database.

### Theorem A: canonical self-state is invariant under an interpretation-only model change

For fixed event history `E`, write `S(E)` for the projection of `assert`, `derive`, and `retract` nodes. If `I_theta(E)` is a set of `interpret` annotations recorded with source model version and without authority over canonical claims, then

`S(E ++ I_theta(E)) = S(E ++ I_theta'(E)) = S(E)`.

*Proof.* The reducer ignores interpretation entries when evaluating evidence-node validity. Its truth values are recursively determined from source assertion status and the conjunction of earlier premises; different derivations with the same proposition provide alternative support. Thus interpretation changes can alter stored narrative annotations and the full-history digest, while leaving the canonical active-node set and canonical digest invariant.

*Boundary.* This is an interface-design invariant, not an inference that model interpretation is behaviorally irrelevant. If a model can author canonical support nodes, the premise fails. Cryptographic authentication and concurrency control are outside this finite reference.

### Theorem B: fixed-size subset-count continuations distinguish all binary histories

For `n >= 2` and `1 <= k < n`, let `x in {0,1}^n`. For every `k`-subset `S` of `[n]`, a future admissible query returns `q_S(x) = sum_{i in S} x_i`. Then the complete query-signature map `x -> (q_S(x))_{|S|=k}` is injective, so any exact fixed-width memory requires **at least `n` bits**.

*Proof.* If `x` and `y` have the same signatures, set `d_i=x_i-y_i`. For distinct `i,j`, choose a `(k-1)`-subset `T` disjoint from `{i,j}` (possible since `k<=n-1`). Equality on `T union {i}` and `T union {j}` gives `d_i=d_j`. All `d_i` equal some constant `c`. Summing any `k` positions yields `k*c=0`, hence `c=0` and `x=y`.

If only the total `sum_i x_i` is observed, there are `n+1` equivalence classes. Within the largest total-count fiber there are `binomial(n, floor(n/2))` histories. For `n=12,k=6`, exhaustive enumeration confirms 4096 distinct subset-count signatures, 13 total-count classes, and largest fiber 924 (requiring 10 additional fixed-width bits conditional on a known total of six).

*Boundary.* The continuation family is expressly **subset-count audits**. This result must not be reported as an exact information bound for arbitrary autobiographical questions, the stochastic posterior of LRM-REV-03, or real language-model memory. It provides a general proof strategy and an independent finite control.

### Theorem C: protected decision margin under adapter succession

Let `m(theta)` be a twice-differentiable decision margin. For update `delta` assume the Hessian operator norm is bounded by `H` at all `theta + s*delta`, `0<=s<=1`. Taylor's integral remainder gives

`m(theta+delta) >= m(theta) - |grad m(theta) dot delta| - (H/2)*||delta||^2`.

For multiple updates `delta_t`, applying the bound at each actual intermediate checkpoint and summing gives

`m(theta_T) >= m(theta_0) - sum_t (|grad m(theta_t) dot delta_t| + (H_t/2)*||delta_t||^2)`.

A positive lower bound preserves the sign of the protected decision margin for the **registered inputs**. Norm caps must apply to the complete segment at each step; measuring only the endpoint Hessian is insufficient. The theorem does not supply those bounds for a neural model.

*Exact counterexample.* `m(a,b)=1/4-a*b`, starting at `(0,0)` with independent updates `(1,0)` and `(0,1)`. Each edit alone yields `1/4`, while their composition yields `-3/4`. The constant Hessian of `-a*b` has spectral norm one. The total update has squared norm two, so the cumulative-start quadratic bound is exactly `1/4-1=-3/4`. Orthogonal parameter updates do not establish functional noninterference.

### Theorem D: bounded external-persona score change bounds distributional change

Fix the same nonempty certified action support and a prior distribution `p` on it. Let score changes `d(a)` satisfy `|d(a)|<=epsilon`, and let

`p'(a) = p(a)*exp(d(a)) / E_p[exp(d)]`.

Then the total variation obeys the **sharp worst-case bound**

`TV(p,p') <= tanh(epsilon/2)`.

More generally, if positive multipliers `w(a)` lie in `[l,u]` with `0<l<=u`, then

`TV(p,p') <= (sqrt(u)-sqrt(l))/(sqrt(u)+sqrt(l))`.

*Proof.* Put `mu = E_p[w]`. Since `TV(p,p')=E_p|w-mu|/(2*mu)` and the absolute-value function is convex, its secant over `[l,u]` upper-bounds `|w-mu|`. Taking expectations gives

`TV <= ((mu-l)*(u-mu))/(mu*(u-l))`.

Maximizing over `mu` in `[l,u]` gives `mu=sqrt(l*u)` and the claimed bound. Setting `l=exp(-epsilon),u=exp(epsilon)` yields `tanh(epsilon/2)`. For multipliers `1,9` and prior probabilities `(3/4,1/4)`, the updated policy is `(1/4,3/4)`, attaining TV `1/2`.

*Boundary.* This bound requires a fixed certified support and common base distribution. Changes to the action vocabulary, evidence/authorization policy, or admissible support are outside its assumptions.

### Corollary E: finite-horizon divergence of persona-driven experiences

Suppose two agent policies have conditional action TV at most `eta` at every matched state/history, with the same environment transition kernel given a matched action. Under a maximal coupling, if trajectories agree up to time `t`, the chance they remain coupled for the next step is at least `1-eta`. Therefore

`P(trajectories diverge by horizon T) <= 1-(1-eta)^T <= T*eta`.

This does not bound the difference between narrative summaries when both trajectories remain matched, nor does it give a nontrivial long-horizon guarantee when the per-step bound is large.

## Related internal work

- `SelfModels/nafsprobe`: causal commitment-summary interventions, and detector false alarms.
- `LoopedTransformers/mechinterp/revision_memory_gym`: LRM-REV-03 continuation signatures and exact posterior enumeration, for a *different* observation law.
- `HybridTRMLDT/docs/cca06_compositional_persona.md`: post-repair covariance identity and Fisher information loss.
- `HybridTRMLDT/docs/rsi_hrm_training_review.md`: principal angles, holonomy, signed-coordinate transport across checkpoints.
- `jinn-or-beast-paper/experiments/ldt_heads_v2_externalized_persona`: learned critical-tag leak; v3 formal critical-tag veto diagnostic.
- `DataGoblin/docs/ldt_independent_shift_v6.md`: circular policy-derived features as a serious architecture-confound control.

## Literature with explicit scope

- Alchourron, Gardenfors, Makinson (1985), *On the Logic of Theory Change*, https://doi.org/10.2307/2274239. AGM is broader than the finite positive-support reducer.
- de Kleer (1986), *An Assumption-Based TMS*, https://doi.org/10.1016/0004-3702(86)90080-9. Alternative justifications and dependency tracking motivate the reference graph.
- Darwiche and Pearl (1997), *On the Logic of Iterated Belief Revision*, https://doi.org/10.1016/S0004-3702(96)00038-0. Historical epistemic state matters for successive revisions.
- Littman, Sutton, Singh (2001), *Predictive Representations of State*, https://papers.neurips.cc/paper_files/paper/2001/file/1e4d36177d71bbb3558e43af9577d70e-Paper.pdf. Future-query equivalence motivates minimal sufficient memory.
- Hu et al. (2021), *LoRA*, https://arxiv.org/abs/2106.09685. Low-rank updates motivate the noninterference question; no LoRA is trained in this artifact.
- Kirkpatrick et al. (2017), *Overcoming Catastrophic Forgetting*, https://doi.org/10.1073/pnas.1611835114. Fisher-style penalties are a prospective neural extension.
- Wang et al. (2026), *A State Change Is Local, Its Consequences Are Not*, https://arxiv.org/abs/2611.02912. Dependency-aware cascading revision in long-term agent memory; our exact graph is a smaller reference model with prespecified edges.

## Next formal and empirical obligations

1. Translate Theorems A-E into Lean with semantics pinned to the Python reducer, independently typecheck, then prove a refinement correspondence between the runtime and the formalization.
2. Add contradictory propositions, time intervals, explicit revocation authority, assumption sets, and versioned plan-state automata; freeze semantics before testing.
3. Bind real NafsProbe records to the canonical source interface without editing historical evidence, and test restarts and injected corruption.
4. Run checkpoint-level adapter experiments only after independent model hashes, heldout task rosters, and uniform or evaluated margin controls are available.

### Lemma F: gauge-invariant one-dimensional subspace transport

For nonzero `u,v` in a real inner-product space, define `s^2 = 1 - <u,v>^2/(||u||^2||v||^2)`. This is the squared sine of the principal angle between their one-dimensional spans; it is unchanged by nonzero scalar rescaling or sign reversal of either basis. Thus comparing sparse decoder atoms by raw signed dot products can overstate feature turnover when a coordinate gauge flips.

For two **unit** simultaneously active feature columns `u,v`, the Gram matrix is `[[1,c],[c,1]]` with `c=<u,v>`. Its eigenvalues are `1+|c|` and `1-|c|`, hence the minimum squared singular value is `1-|c|`. In our rational example `u=(1,0)`, `v=(9999/10001,200/10001)`, both norm one, so the smallest squared singular value is exactly `2/10001`. Individually each feature is perfectly conditioned; their joint inverse is poorly conditioned. This is a two-dimensional capacity witness, not a fitted SAE or observed LLM mechanism. Related internal work: `Compactification-Theory/research/curved_sae_gauge_v1/SAU_CURVE02_RESULTS.md`.

### Proposition G: certified-support containment under external persona succession

Let the canonical projection supply a trusted admissible action set `C(S)`. For arbitrary nonnegative prior weights and strictly positive persona multipliers, normalize the reweighted policy **only over actions in** `C(S)`. Its support is a subset of `C(S)` for every persona version. If `C(S)` is empty, return an abstention/no-action outcome. This is immediate from multiplication by the certified-support indicator, provided the state reducer and authorization evidence are trustworthy. A model-authored interpretation annotation alone cannot add `authorized:*` claims in the finite reference. The result is a local interface invariant, and says nothing about whether an action's real-world semantics or the underlying verifier is correct.

## v0.2: implementation and proof obligations, 20 November 2026

**SQLite-to-event projection.** The legacy NafsProbe schema is one mutable JSON snapshot per run. `nafsprobe_bridge.py` implements a read-only typed projection of current fields; the `nafsprobe_sidecar.py` output records the sequence of *observed snapshots*, with field-level replacements expressed as a `retract` of the previously observed assertion followed by a new `assert`. This is a new evidence wrapper for research use, not a recovery of the original source-event history.

**Proposition H (observational projection consistency, conditional).** If the source JSON validates and no sidecar corruption is present, the sidecar's canonical claim set after a successful synchronized observation equals the canonical claim set obtained by directly translating that observed NafsProbe snapshot. The algorithm explicitly checks equality before committing and the audit replays each recorded prefix. For a reflection-only revision of the same canonical fields, the canonical claim digest remains invariant while the full chain tip changes. The claim is tested in Python using temporary SQLite databases, including restarts and forged-text annotations; a Lean refinement theorem is still outstanding.

**Integrity boundary.** SHA-256 here checks byte consistency and event-chain consistency. It is not a signature or trusted timestamp. A process with permission to replace both source and sidecar databases can forge a new internally consistent history. The sidecar stores untrusted model text in annotations and never interprets that text as a permission. The read-only source adapter has no authenticated evidence of who changed a historical record.

**Lean scope.** `formal/ContinuityV1.lean` formalizes the *canonical-stream filtration* behind Theorem A, a certified-support membership property behind Proposition G, and small exact witnesses used in C, E, and F. It does not yet model the entire runtime dependency DAG or prove the general analytic bounds B-E. Its Lake package is included for CI checking; Lean is unavailable in this local artifact environment, so proof typechecking has not been claimed.

## v0.3: event collector refinement and cumulative adapter preservation (21 November 2026)

### Theorem I: fold collection refines a separately recursive event specification

Let `FiniteEvent` have `base(id, claim)`, `derived(id, claim, premises)`,
`revoke(id, target)`, and `note(id, version, text)` constructors. Define two
representations of the same finite stream:

- `compile(E)`: left-to-right event ingestion into node, revoked-source, and
  annotation lists, appending records in observed order;
- `spec(E)`: three independent structural recursions over `E`, one for each
  category (nodes, revoked targets, and annotations).

For any prefix accumulator `a`,

```
compileFrom(a,E) =
  (a.nodes ++ specNodes(E),
   a.revoked ++ specRevoked(E),
   a.annotations ++ specAnnotations(E)).
```

*Proof.* Induction on the event list. The empty stream leaves the accumulator
unchanged. Each constructor appends to exactly one category, and the inductive
step uses associativity of list append. Specializing to the empty accumulator
gives `compile(E)=spec(E)`.

Let `active(N,R)` scan the ordered evidence nodes with the **final** revoked
source set `R`: an assertion is active iff its identifier is absent from `R`;
a derivation is active iff every premise was active at its earlier node
position. Because both collector forms produce equal node and revocation
lists, their computed active identifiers and claims are equal. Appending a
`note` changes only annotations, so neither canonical active IDs nor claims
change. Independent support paths survive retraction of a different path.

The statements are encoded in
`formal/ContinuityV1/Refinement.lean` as
`collectFrom_refines`, `compiled_refines_specification`,
`activeIDs_refine`, `activeClaims_refine`, and annotation invariance theorems,
with concrete alternative-support examples.

**Correspondence boundary.** Python `core.replay` uses unique *string* event
identifiers, rejects malformed references, sorts active IDs, deduplicates and
sorts claims, and hashes JSON bytes. The Lean event type uses natural-number
IDs and records the ordered list of active IDs and claims. The mathematical
correspondence to Python requires a unique injective ID renaming and its
validation assumptions (earlier premises, retracting an assertion only).
Active claim correspondence is set-theoretic after sorting/deduplication. The
Lean theorem proves two *Lean semantics* equivalent; it is not a mechanically
verified refinement of Python, SQLite, SHA-256, or the source-import boundary.
`refinement_checks.py` independently evaluates the Python positive-support
DAG by recursive premise traversal, after collecting all base retractions.
The test suite compares that oracle to actual `core.replay` on every six-source
retraction pattern and 60 deterministic random DAGs, plus the concrete Lean
examples. These executable comparisons support the cross-language mapping,
without replacing a verified compiler or source-level formal extraction.

### Theorem J: cumulative adapter-margin preservation under local loss caps

Let a protected decision margin at successive checkpoints be
`m_0,m_1,...,m_T`. Assume exact bounds `m_i <= m_(i+1) + c_i`
for every adjacent checkpoint pair in **actual order**. Summing the
inequalities yields

```
m_0 <= m_T + sum_i c_i.
```

Therefore `sum_i c_i < m_0` implies `m_T > 0`. This is a property of any
finite sequence of certificates, independent of the method used to produce
them. The finite-inductive proof is in
`formal/ContinuityV1/AdapterSuccession.lean` as
`marginPath_sound` and `marginPath_preserves_positive`.

For a twice differentiable protected margin `m(theta)`, a sufficient
local loss cap follows from Taylor's theorem when a uniform Hessian operator
norm bound `H_i` holds on the **entire segment**
`theta_i + s*delta_i, 0 <= s <= 1`:

```
c_i = |grad m(theta_i) . delta_i| +
      H_i * ||delta_i||^2 / 2.
```

The gradient must be re-evaluated after each earlier adapter edit. A model
that switches routing, composes LoRA modules nonadditively, or changes the
protected margin definition requires its own segment-specific analysis.
For integer-scaled rational margin and budget certificates, the Lean theorem
applies directly; choose a common positive denominator before scaling.

`adapter_succession.py` checks these bounds using exact rational arithmetic,
ensures the linked checkpoints and margins form a chronological path, and
returns a structured **conditional** certificate. It checks consistency of
supplied numbers but cannot independently establish the Hessian premise,
exact model hashes, or genuine measured neural margins. Such receipts should
not be promoted to model-safety certificates.

**Noninterference counterexample.** The fixed bilinear margin
`m(a,b)=1/4-a*b` equals `1/4` after either unit coordinate edit in isolation,
while their sequential combination yields `-3/4`. Its Hessian is
`[[0,-1],[-1,0]]`, with operator norm 1. The exact mixed finite difference
is `-1` in the fraction-valued representation, or `-4` in the integer
numerator used by Lean. Independent adapter tests are thus inadequate for
certifying composition; every checkpoint transition needs a new bound.

**Kernel status:** The v0.3 Lean modules were authored against the Lean 4
`v4.24.0` `Init` library and added to the Lake build. Local Linux has no
Lean toolchain and network DNS is unavailable. The Lean theorems have
**not** been kernel-checked in this environment. The CI workflow is prepared
for future verification. Python tests and exact arithmetic are separately
executable now.

# PGC-01 / NCG-01: operational reconstruction and its limits

26 November 2026. This note collects the mathematical claims, finite witnesses, and physical obligations from the parallel research branches. The referenced commits pin the evidence predating this synthesis.

## 1. Operational influence

Given declared subsystem factors A and B, a preparation rho, allowed local trace-preserving channels Phi and Psi, and a subsequent evolution T_t, define I(A -> B;t) as the supremum of half the trace norm of the difference between the two reduced B states after evolution. The supremum ranges over the admitted preparations and interventions. At t=0, disjoint factors and unconditional local trace-preserving channels imply zero influence. Later evolution can produce nonzero influence. This definition presupposes subsystem access, a dynamical parameter, and the relevant operations; none of these is derived by the definition.

For an affine Boolean update x -> Mx+b over F_2, a single-coordinate flip produces the exact difference M^t e_i after t updates. The cancellation fixture F(x0,x1,x2,x3)=(0,x0,x0,x1 XOR x2) exhibits influence along each of two routes but zero net source-to-target response after two steps. An intervention on an intermediate register changes the experiment and can restore the response. Consequently, transitive closure of measured dependence cannot automatically be identified with operational influence.

The exact experiment reports 4,164 affine systems, 443,916 paired response comparisons and 111,372 independent matrix-power influence checks, alongside nonlinear fixtures and permutation checks.

Evidence: [Compactification Theory PGC-01](https://github.com/MoralityLabAI/Compactification-Theory/tree/91ee1ac00b0a849c62f7c08b98f4eb969d094079/research/pregeometric_compactification), [CI](https://github.com/MoralityLabAI/Compactification-Theory/actions/runs/45802178724).

## 2. Observation fibers and certificates

For admissible worlds W, observation map o:W -> R and property p:W -> P, exact decoding requires p to be constant on every fiber of o. If o(w)=o(v) and p(w) differs from p(v), every deterministic decoder of the record fails on at least one of the two worlds. Deterministic postprocessing preserves this witness. Conversely, if p is constant on fibers, it defines a unique map on the image of o; extending to all R requires suitable defaults outside that image.

The Lean module MathCan/OperationalIdentifiability.lean checks four related statements with empty printed axiom dependency lists. The converse on the image is a mathematical observation here, with no additional Lean verification claimed.

The finite observer task asks whether a Boolean response f(x,z) depends on x in some context z. Twelve of the sixteen truth tables are dependent, so the uniform prior yields 75% accuracy even at zero queries. Four queries are necessary in the worst case for certainty, since any unqueried entry of an independent truth table can be flipped to yield a dependent completion. Querying the two entries for one context first detects dependence if they differ; otherwise the second context is queried. This yields three queries in expectation under the uniform prior. The experiment reports eight sufficient observer states, with external query access and transition-program costs accounted for separately. It checks 81 partial truth tables and compares against adaptive policy enumeration.

Evidence: [SelfModels PGC-01](https://github.com/MoralityLabAI/SelfModels/tree/a65ffab7ce5a0ce0a6044b37d5f15fc869921fd8/research/pregeometric_observer), [CI](https://github.com/MoralityLabAI/SelfModels/actions/runs/45802181541), [MathCan Lean CI](https://github.com/patrickdugan/MathCan/actions/runs/45802186706).

## 3. Null-cone trace argument

For a positive operator W on a Hilbert space H, if W >= m I for m>0 and Tr(W)=Z is finite, any orthonormal family of N vectors obeys Nm <= Z. Thus dim H <= floor(Z/m). The key requirement is a uniform strictly positive lower bound, or another justified argument excluding arbitrarily small weights. Finite entropy or charge matching alone supplies no such bound. For instance, a diagonal density operator with entries 2^(-n), n>=1, has unit trace and finite entropy (2 log 2 in nats) yet infinite rank.

The NCG-01 audit provides rational countermodels and Lean finite-sum lemmas for scaled natural weights. Its four Lean lemmas carry the printed dependencies propext and Quot.sound; the full operator theorem is presented in prose.

Evidence: [MathCan NCG-01](https://github.com/patrickdugan/MathCan/tree/35b22335e057c4ce3f1343d8b1a0621cbbf5b34f/research/null_cone_audit), [CI](https://github.com/patrickdugan/MathCan/actions/runs/45800300546). The companion [boundary constraints and gluing gym](https://github.com/MoralityLabAI/Compactification-Theory/pull/305) and [BPD steering pilot](https://github.com/MoralityLabAI/BPD/pull/158) are computational applications; the latter reports -1.367 percentage points on the primary comparison and a pilot/redesign-only verdict.

## 4. Physical reconstruction obligations

| Target | Required bridge |
| --- | --- |
| Lorentzian manifold | Primitive dynamics and a controlled continuum limit yielding smooth local geometry with Lorentzian signature. |
| Universal null cones | Derived characteristic structure and agreement across physical sectors. |
| Four dimensions | A selection principle over competing dimensions, with scale-dependent estimators and a continuum justification. |
| Einstein variables and equations | A justified map from primitive observables to metric, tetrad or connection and an effective dynamical principle. |
| Newton coupling | A dimensionless prediction relative to independently specified scales, or a microscopic area-entropy coefficient with units fixed. |

The target paper [arXiv:2611.34924](https://arxiv.org/abs/2611.34924) starts from four-dimensional Lorentzian vacuum GR with finite Newton coupling. Jacobson's [thermodynamic argument](https://arxiv.org/abs/gr-qc/9504004) relates Newton's constant to an entropy-area coefficient eta: G=c^3/(4 hbar eta) when S/k_B=eta A and the stated equilibrium and local horizon assumptions hold. A microscopic derivation still needs to determine eta and the physical area scale.

The observation-fiber theorem gives a precise way to audit each proposed bridge: specify the admissible models, the record map and the target invariant. Find a pair with equal records and differing targets, or prove constancy on fibers. The finite Boolean experiments establish examples in their declared classes; they do not establish a physical continuum limit or select the dimension of our universe.

## 5. Proposed next experiment (unrun)

PGC-02: compare coordinate-free records of finite event structures across candidate effective dimensions, using matched-size and matched-degree controls. Freeze the observation map and dimension estimator before evaluation. Include indistinguishable model pairs where possible, report the set of compatible dimensions and certificate coverage, and test stability as the observation horizon grows. Any geometry used in generating reference examples must be marked as supplied. Treat a four-dimensional preference as a separate hypothesis requiring a justified dynamics or ensemble, rather than as a consequence of the classifier.

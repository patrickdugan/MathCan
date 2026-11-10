# LVR-01: Intervention quotients, bounded observation, and stochastic error

**Status:** Mathematical propositions with proofs and finite exact checks (2026-11-10). The systems are digital finite-state models. The mathematical extensions are authored for MathCan and are not attributed to Michael Levin.

**Research motivation:** [Levinverse's integration map](https://github.com/patrickdugan/levinverse/blob/aca03112c722af237940118f22204b4b6ca5dc87/research/integration.md) asks how anatomical outcomes, available interventions, and multiscale controllability might be related. Its [UChicago appearance note](https://github.com/patrickdugan/levinverse/blob/aca03112c722af237940118f22204b4b6ca5dc87/research/summaries/uchicago-big-brains-2023.md) separates the speaker's biological interpretations from independent evidence. The related finite deterministic quotient is already described in [XenobotBench MOP-01](https://github.com/patrickdugan/XenobotBench/blob/42e7027117ddc67daffc40e83516de67972b54df/docs/MORPHOSPACE_QUOTIENT.md). This note adds an explicit *history-distribution* robustness bound for a stochastic abstraction and provides exact tests.

## 1. Finite intervention-relative identity

Let `S` be a finite state set, `A` a finite menu of actions, `F_a:S→S` deterministic, and `o:S→O` an observation. For a finite word `w` in `A*`, apply its actions from left to right and call the resulting map `F_w`.

Define `s ≈_A t` when `o(F_w(s)) = o(F_w(t))` for every `w ∈ A*`, including the empty word. This is the greatest action-stable equivalence that respects the current readout.

**LVR-01/T1 (finite refinement and bounded witness).** Partition first by `o`. Repeatedly refine each class with the vector of its successor-class labels for every action. With `n=|S|` and `k₀` initial observation classes, the process makes at most `n-k₀` strict refinements. Its stable classes are precisely `≈_A`. Every inequivalent pair has a distinguishing word of length at most `n-k₀`, hence at most `n-1` when `S` is nonempty.

*Proof.* After round `j`, equality of classes means equality of observations after all words of length at most `j`; prove by induction by peeling off the first action. Any strict refinement increases the class count by at least one. Once the partition is stable, action stability propagates agreement to arbitrary future words by induction on their length. A pair first separated by round `j` has a witness of length at most `j`. This is the classical Moore-machine partition-refinement argument, also given in MOP-01.

**LVR-01/T2 (intervention-menu monotonicity).** If `A ⊆ B`, with the same transition rule for shared actions, then `≈_B` refines `≈_A`. Enlarging the experiment interface cannot decrease the number of distinct behavioral classes.

*Proof.* Every word over `A` is also a word over `B`. Equality for all `B` words therefore implies equality for all `A` words.

**LVR-01/T3 (observation coarsening).** If `o₂ = h ∘ o₁`, then equivalence under `o₁` refines equivalence under `o₂`, for a fixed action menu.

*Proof.* Apply `h` to each equality of the fine readout. The number of equivalence classes can only fall or remain constant.

In both statements the readout and permitted action menu form part of the identity specification. These are observation-interface statements, without an ontological conclusion about biological individuality.

## 2. A stochastic simulation lemma for observable histories

Let `q:S→Y` be a finite quotient map, `K_a(s,·)` a probability kernel on microstates, and `L_a(y,·)` a proposed macrostate kernel. Assume, uniformly for every state `s` and allowed action `a`, that

\[
\operatorname{TV}\big(q_{\#}K_a(s,\cdot), L_a(q(s),\cdot)\big)\le\varepsilon,
\quad 0\le\varepsilon\le 1.
\]

Here `TV(μ,ν) = (1/2)Σ_x |μ(x)-ν(x)|`. Both processes start from `y₀=q(s₀)`. A policy chooses actions using **only the macro-observation history**, possibly with shared randomization, with the same rule in both processes.

**LVR-01/T4 (adaptive history coupling).** For the laws `P_T` and `Q_T` of complete observed histories `(y₀,…,y_T)`, under the micro and macro processes respectively,

\[
\operatorname{TV}(P_T,Q_T)\le 1-(1-\varepsilon)^T\le\min(1,T\varepsilon).
\]

*Proof.* Couple initial observations exactly. Whenever their macro-histories agree, couple the policy's action draws identically. Conditioned on a fixed microstate, the micro successor's observed distribution lies within TV `ε` of the macro successor. Conditioning on the shared observed history makes the micro successor a mixture of those rows; convexity of TV preserves this bound. A maximal coupling succeeds in keeping the next macro observations equal with probability at least `1-ε`, conditional on agreement so far. Thus the probability of fully matched histories is at least `(1-ε)^T`. The coupling inequality gives the stated bound. Bernoulli's inequality gives the linear upper bound.

**LVR-01/T5 (bounded outcome and cumulative value).** For every measurable `g` on complete observed histories with `0≤g≤1`,

\[
|\mathbb E_Pg-\mathbb E_Qg|\le1-(1-\varepsilon)^T.
\]

If a bounded reward `r_t∈[0,1]` is read from history at each step `t=1,…,T`, then

\[
\left|\mathbb E_P\sum_{t=1}^T r_t-\mathbb E_Q\sum_{t=1}^T r_t\right|
\le\sum_{t=1}^T [1-(1-\varepsilon)^t]
\le \tfrac12\varepsilon T(T+1).
\]

*Proof.* The difference of expectations of a `[0,1]`-valued function is bounded by TV. Apply T4 to each prefix, followed by the triangle inequality.

**LVR-01/T6 (sharpness).** Both the exponential-coupling expression and its interpretation as a history error are attainable. Let the micro chain stay at `0` forever, while the macro chain starting at `0` jumps to absorbing `1` with probability `ε` on each step. Set the micro transition at `1` to be absorbing too, so the one-step defect is exactly `ε`. After `T` steps the micro history is all zeros; the macro history has that value with probability `(1-ε)^T`. Their total variation is exactly `1-(1-ε)^T`.

## 3. Scope and evaluation use

This bound applies to an abstraction that passes a **uniform one-step pushforward defect** test. Errors measured only on training-state averages cannot instantiate the uniform premise. The policy must use the quotient-visible history; access to hidden microstate makes the coupling proof inapplicable as written. Long-horizon fidelity can deteriorate even when the one-step defect is small.

A useful evaluation would hold out new action words and compare full observed-history distributions, not only terminal morphology labels. Measure the empirical defect, path-TV bound, and goal-event probabilities on synthetic control systems before testing any scientific analogy.

## 4. Reproduction

Run from the MathCan repository root:

```sh
python -m unittest tests.test_levinverse -v
```

`finite_interventions.py` implements partition refinement, shortest witness search, exact rational TV, and history-law comparison. The test suite exhaustively covers **5,832** three-state, two-action, binary-observation transition/readout specifications, and includes exact stochastic tightness and adaptive-policy checks. The resulting proofs are mathematical; finite testing checks the implementation and examples.

# SPC-05: phase-localized recurrence and causal subspace dimension

Date: 15 November 2026. Continuation of SPC-04, using its independently archived trained checkpoints. These are **new statements and proofs for this campaign** assembled from standard linear-algebraic and dynamical ingredients. Mathematical priority has not been established. The headline theorems of the motivating OpenAI Math preprints are neither assumed nor claimed to imply the neural results.

Source pair: OpenAI Math 2026 [#129, *An exponential two-way deterministic state lower bound for one-way liveness*](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026) motivates exact distinctions between states that future queries can separate. [#130, *Finite tensor savings and exact Fourier circuits*](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026) motivates separating full-state dimensions from the Fourier/phase structure. The proofs below are independent of the source papers' automata and circuit-size claims.

## A. The empirical object and an exact semigroup control

The native `LoopedChase` recurrent map is autonomous after fixing the input prompt:

\[
        h_{t+1}=F_e(h_t),\quad h_t=(c_t,a_t)\in\mathbb R^{8\times48}\oplus\mathbb R^{48}.
\]

The context block `c` consists of the eight edge-token states, while `a` is the answer-token state. The prompt injection `e` is fixed throughout an intervention. The archived SPC-04 checkpoints have trained model seeds 41522 and 41523 (48-wide, one tied block, three supervised hops). Intervention depth is 64 and the observation interval is 12 loops. Held-out graph seeds `905501,905502,905503`, each with 64 items per checkpoint, are disjoint from the original training and the SVD-fitting prompts.

**Lemma 1 (temporal phase transplant).** For any map \(F:X\to X\), any \(s,t\in\mathbb N\), and any \(x\in X\),

\[
                F^t(F^s(x))=F^s(F^t(x))=F^{t+s}(x). \tag{1}
\]

**Proof.** Composition of successive applications of a fixed function is associative. Induction on \(t\) establishes the equality. The result holds without differentiability, contraction, or periodicity assumptions. It explains why transplanting the **entire** future state is a sanity check for the simulator, rather than a discovery about neural phase storage. `MathCan/PhaseLatch.lean` proves (1) for arbitrary types in Lean.

For each prompt, a cycle is *registered* only if its graph-derived integer pointer period \(p>1\), its full-state relative return error \(\|h_{t+p}-h_t\|/\|h_t\|<10^{-4}\) at the evaluation depth, its one-step error is above \(0.05\), and its phase-reference separation exceeds \(10^{-8}\). The phase classifier compares the perturbed full state against every unperturbed phase \(h_{t+j}\), \(0\le j<p\). All other cases remain counted as unregistered; task success and phase registration are distinct diagnostics.

Across 384 held-out prompt/checkpoint cases, 288 meet that registered criterion. Swapping only the answer-token state from depth 65 into depth 64 places **288/288** registered cases in the phase-\(+1\) reference basin after 12 recurrent updates. Replacing only the context-token states from depth 65 leaves **288/288** at phase zero. These are numerical phase-nearest findings under the declared classifier, with no claim that a learned phase manifold has been analytically proven.

## B. Orthogonal energy law for partial-state transplants

Take a real Hilbert direct sum \(X=C\oplus A\), and states \(x_0=(c_0,a_0)\), \(x_1=(c_1,a_1)\). Define the answer hybrid \(z_A=(c_0,a_1)\) and context hybrid \(z_C=(c_1,a_0)\).

**Proposition 2 (exact hybrid separation).**

\[
\begin{aligned}
\|z_A-x_1\|^2&=\|c_1-c_0\|^2,&
\|z_A-x_0\|^2&=\|a_1-a_0\|^2,\\
\|x_1-x_0\|^2&=\|c_1-c_0\|^2+\|a_1-a_0\|^2.
\end{aligned}\tag{2}
\]

**Proof.** Evaluate the orthogonal direct-sum norm coordinatewise. Consequently, the answer hybrid is closer to the next phase than to the current phase **among those two candidates** precisely when the answer accounts for over half the squared phase displacement. This distance test by itself does not guarantee attraction or beat other phase candidates. Lean verifies the integer two-coordinate specialization in `MathCan/PhaseLatch.lean`.

At depth 64, the answer token contributes roughly 96% and 79% of phase-step displacement energy for the two models, with substantial prompt variation. To control for the different sizes of context and answer swaps, SPC-05 also injects equal Euclidean-norm Gaussian perturbations, scaled as a fixed fraction of minimum interphase distance: at fraction 0.75, **244/288** registered trajectories retain phase zero after answer-token noise, versus **288/288** under context-token noise. Both interventions have the same total initial Euclidean norm for each prompt.

## C. A forced-context polynomial phase latch

Define for \(|\lambda|<1\) and \(\beta\in\mathbb R\)

\[
 f(a)=1-3a^2+2a^3,\qquad
 F(c,a)=(\lambda c+\beta a, f(a)).\tag{3}
\]

**Theorem 3 (phase-key control with exponential context repair).** Let

\[
 c_0=\frac{\beta}{1-\lambda^2},\quad
 c_1=\frac{\lambda\beta}{1-\lambda^2},\quad
 x_0=(c_0,0),\quad x_1=(c_1,1).
\]

Then \(F(x_0)=x_1\) and \(F(x_1)=x_0\). Both are locally attracting phase states under the two-step return map. With hybrids \(z_A=(c_0,1)\) and \(z_C=(c_1,0)\), for every integer \(t\ge0\) there are exact identities

\[
\begin{aligned}
 \operatorname{pr}_A F^t(z_A)&=\operatorname{pr}_A F^t(x_1),&
 \operatorname{pr}_C\big(F^t(z_A)-F^t(x_1)\big)&=\lambda^t(c_0-c_1),\\
 \operatorname{pr}_A F^t(z_C)&=\operatorname{pr}_A F^t(x_0),&
 \operatorname{pr}_C\big(F^t(z_C)-F^t(x_0)\big)&=\lambda^t(c_1-c_0).
\end{aligned}\tag{4}
\]

**Proof.** Direct substitution into (3) gives \(f(0)=1\) and \(f(1)=0\), yielding the exact two-cycle. The answer inputs of \(z_A\) and \(x_1\) agree. Their future answer coordinates therefore coincide by induction; the context discrepancy evolves according to \(d_{t+1}=\lambda d_t\), establishing the first line of (4). The second follows identically. At either cycle point,

\[
 DF=\begin{pmatrix}\lambda&\beta\\0&0\end{pmatrix}
\]

because \(f'(0)=f'(1)=0\). The full-cycle monodromy is

\[
 D(F^2)=\begin{pmatrix}\lambda^2&\lambda\beta\\0&0\end{pmatrix},
 \qquad \rho(D(F^2))=\lambda^2<1.
\]

The fixed-point criterion for the two-step return map implies local attraction, and (4) gives an exact repair rate along the hybrid perturbations. All identities are independently checked using `fractions.Fraction` in `tests/test_phase_latch.py`. The finite Boolean forced-context model is also kernel-checked in Lean. This construction is an explicit illustrative skew-product, not a reverse-engineered proof of the transformer's update rule.

## D. Phase-contrast dimension and a certified low-rank swap criterion

**Theorem 4 (contrast-space bound).** Suppose a model represents one of \(q\) discrete phases by fixed codewords \(v_0,\ldots,v_{q-1}\) in a real vector space \(V\). Their pairwise phase contrasts span a subspace of dimension at most \(q-1\).

**Proof.** Each contrast factors through a common anchor:

\[
         v_j-v_i=(v_j-v_0)-(v_i-v_0).\tag{5}
\]

There are at most \(q-1\) nonzero anchor contrasts. Thus the span of all differences is contained in the span of \(v_1-v_0,\ldots,v_{q-1}-v_0\), establishing the bound. Lean proves (5) coordinatewise for arbitrary finite index sets. Fixed codewords are an explicit premise: graph-conditioned or transient phase representations may occupy a larger pooled span. With eight possible node labels, the ideal fixed-code contrast bound is seven dimensions.

**Proposition 5 (projection-to-phase certificate).** Let \(G=F^t\), let \(x_1=x_0+\delta\), and let \(P\) be an orthogonal projector. Suppose \(G\) is \(L\)-Lipschitz along the segment joining \(x_1\) to \(x_0+P\delta\). Then

\[
 \boxed{\|G(x_0+P\delta)-G(x_1)\|\le L\|(I-P)\delta\|.}\tag{6}
\]

Let \(T\) be the desired actual phase-\(+1\) reference state at the intervention depth, and let \(\eta=\|G(x_1)-G(T)\|\) measure the answer-only hybrid's error relative to the full future-state transplant. The projected intervention satisfies

\[
 \|G(x_0+P\delta)-G(T)\|\le \eta+L\|(I-P)\delta\|.\tag{7}
\]

If \(G(T)\) is separated by at least \(\Delta>0\) from all competing output-phase references and \(2(\eta+L\|(I-P)\delta\|)<\Delta\), the projected intervention is uniquely classified as phase \(+1\) by nearest-reference distance.

**Proof.** The two projected-swap inputs differ by \((I-P)\delta\). Apply Lipschitzness to obtain (6), followed by the triangle inequality to get (7). For any competing phase \(y\), the reverse triangle inequality bounds its distance from the projected output below by \(\Delta-(\eta+L\|(I-P)\delta\|)\), which exceeds the bound in (7). Equality in (6) is possible for the identity map along a discarded direction. In the neural experiment \(\delta\) is the **answer-only transplant increment**; the mismatch \(\eta\) accounts for the untransplanted context. Thus the stated criterion applies to the actual full-phase reference.

The uncentered train-only SVD of phase differences minimizes the total squared *training* projection residual among fixed-rank linear subspaces. Its guarantee does not automatically extend to held-out prompts or bound the nonlinear \(L\); those are experimental questions.

## E. Frozen, held-out causal subspace experiment

The code fits the answer-token SVD on 256 independent prompts at recurrent depths 32,48,64, giving 768 phase-increment rows per model. No labels, readout gradients, or held-out prompts are used in the basis. The rank grid is \(2,4,7,8,12,16\). For each rank, eight deterministic random orthonormal subspaces serve as controls. Both raw projected increments and increments rescaled to the exact full-answer swap norm are tested. Each perturbation is followed for 12 loops on the **same fixed prompt**.

Only the 288 numerically registered nonfixed pointer cycles receive phase-identification credit. The raw SVD-projected transplant results are:

| rank | raw SVD phase +1 | random norm-matched phase +1 across 8 trials |
|---:|---:|---:|
| 2 | 76/288 | 18–34/288 |
| 4 | 167/288 | 30–50/288 |
| 7 | 287/288 | 40–58/288 |
| 8 | **288/288** | **45–70/288** |
| 12 | 287/288 | 63–104/288 |
| 16 | 287/288 | 91–132/288 |

The 8-dimensional basis accounts for 97.9505% and 98.5568% of the respective models' **training** phase-increment energy. The near-perfect seven-dimensional result is consistent with Theorem 4's fixed eight-codeword contrast geometry, while the residual directions could encode prompt dependence, model error, and nonlinearity. The eight-dimensional result is an intervention success rate, not a proof of a uniquely identified eight-neuron circuit.

The statistics share model weights and prompts across randomized controls; each row is a descriptive finite cohort, not an independent large-model replication. A future control should learn the same causal basis on one task family and test transfer under novel graph distributions, wider node sets, and trained checkpoint architectures.

## F. Verification and limitations

- `MathCan/PhaseLatch.lean` checks the generic semigroup identity, pairwise hybrid squared distances, the anchor-contrast relation, and a finite Boolean phase latch. The analytic contraction, spectral-radius, Lipschitz, and dimension theorems are proved above as mathematical arguments and **are not claimed as Lean kernel theorems**.
- `tests/test_phase_latch.py` independently verifies the exact rational skew-product over multiple parameters, including negative contraction rates.
- `LoopedTransformers` stores the frozen SHA-verified checkpoint manifest, source tests, and compact JSON receipts; binary trained weights remain in the attached SPC-04 experiment archive.
- The intervention uses future state from the **same** source input as an oracle counterfactual. It is a causal diagnostic of hidden-state phase location and not a deployable predictive control policy.
- This work uses synthetic 8-node pointer chasing with two trained 48-wide models. It demonstrates localized computation-phase control within that scope. No larger-LM generality, semantic knowledge, or safety claim follows.

## G. A necessity theorem for continuous phase-subspace ablation

The sufficiency experiment transplants a low-rank answer-phase update. A distinct causal question asks whether the learned phase subspace is **necessary for continued recurrent outputs**. Start after the third supervised update and suppress only the answer-token increment projected onto the previously learned rank-seven SVD basis at each later loop. Keep the context states and the fixed graph prompt updated normally.

**Theorem 6 (projected increment suppression freezes projected readout).** Let \(P:A\to A\) be a linear projection, \(P^2=P\), and let \(F_e:C\oplus A\to C\oplus A\) be any recurrent update. Define a controlled update by

\[
 \widetilde F_e(c,a)=(c',\,a+(I-P)(a'-a)),\qquad (c',a')=F_e(c,a).
 \tag{8}
\]

Then every controlled trajectory satisfies \(Pa_t=Pa_0\). For any readout that factors as \(R(c,a)=\rho(Pa)\), the output \(R(\widetilde F_e^t(c_0,a_0))\) is constant for all \(t\ge0\), even as the complement of \(P\) and the context coordinates change.

**Proof.** Since \(P^2=P\), applying \(P\) to the second component of (8) gives

\[
 P[a+(I-P)(a'-a)]=Pa+(P-P^2)(a'-a)=Pa.
\]

Induction on time proves \(Pa_t=Pa_0\). The asserted readout equality follows by evaluating \(\rho\) at this fixed value. In `MathCan/PhaseLatch.lean`, the theorem is kernel-checked for a generic key/context pair by replacing the key with its previous value after each arbitrary context update. It is an instance of (8) for a coordinate projector; the general Hilbert-space statement remains a written proof.

**Held-out empirical counterfactual.** For the same 384 prompts and two fixed SPC-04 checkpoints, evaluate at depths 6, 12 and 24 after starting subspace suppression at step 4. Using the frozen rank-seven PCA basis, every output matches the model's **loop-3 readout** on all 384 prompts at all three depths. The rank-eight ablation gives the same result. Hidden states continue evolving in the orthogonal complement. Unintervened current-hop accuracy at depth 6 is 382/384, while rank-seven suppression gives 92/384, exactly the count achieved by freezing the entire answer token. The latter number is not interpreted as chance accuracy: on small permutation cycles, hop 3 can coincide with hop 6.

A rank-eight *random* ablation in the same 48-dimensional answer space gives 276–332 correct answers at depth 6 over eight random bases. When random ablations remove the same total increment norm as the learned rank-eight projector, only 120–144 remain correct; these controls generally **fail to freeze** the readout to its initial value. The controlled direction therefore matters, and raw performance loss from a large-magnitude intervention alone does not establish phase-specific mechanism.

Theorem 6 is a sufficient condition, not a proof that the actual nonlinear LayerNorm readout globally factors through this PCA subspace. Its near-exact empirical freeze on the tested inputs indicates that the readout along these controlled trajectories behaves as if the phase-bearing component were conserved. To establish a global mechanistic account, estimate the readout's sensitivity to complementary directions and repeat on out-of-distribution graphs.

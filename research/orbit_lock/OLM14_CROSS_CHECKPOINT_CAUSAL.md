# OLM-14: Identifiability limits and calibrated tests for cross-model causal transfer

November 16, 2026. Pure mathematical companion to SMC-14, following [OLM-13](OLM13_ORBIT_AND_FACTOR_GAUGE.md) and the frozen SMC-13 source-locked observation that independently trained recurrent Sudoku teachers exhibit activation correspondence after conditioning on visible clues.

The claims below are classical linear algebra and finite-difference calculus applied to a new exact experimental contract. Mathematical priority beyond this specific construction is not established. These are written proofs with independent exact-rational regression witnesses, rather than Lean kernel formalizations.

## 1. Observational feature alignment cannot identify an intervention

Fix two teachers with hidden states \(h^A,h^B\), sparse encoders \(Z_A,Z_B\), and task-relevant scalar output margins \(m_A,m_B\). The calibration algorithm can use arbitrary joint statistics of the encoder activations and all visible input variables, but it cannot inspect output derivatives without an intervention.

**Theorem OLM-14A (causal nonidentifiability under perfect activation alignment).** Even exact equality of sparse feature activations on every input, matching unperturbed task labels, and equal unperturbed classification accuracy do not determine the sign of a matched feature's causal effect.

**Proof by construction.** Use one shared hidden scalar \(h\in(0,1)\) and the identical positive ReLU feature \(Z_A(h)=Z_B(h)=h\). Let \(C=3\) and let the two-digit true-label margins be
\[
m_A(h)=C+h,\qquad m_B(h)=C-h.
\]
Both margins are strictly positive throughout the full input domain, so the teachers predict the same target digit on every example. Their complete observed activation distributions, including any conditioning on visible inputs, agree exactly. Under the same signed unit hidden intervention, their directional derivatives are \(+1\) and \(-1\). Any feature assignment obtained solely from activation cooccurrence must be identical in the two possible worlds, yet the causal sign differs. QED.

This obstruction remains relevant when cross-model SAE feature assignments are chosen by calibration-only Hungarian matching. A high held-out activation overlap is evidence of observational transfer, and it supplies no causal sign theorem without additional assumptions.

## 2. Fixed digit margin and finite-radius causal derivative

For a frozen teacher \(T\), puzzle \(p\), and missing goal token \(g\), let \(F_T(h)\in\mathbb R^{10}\) denote the final goal-token logits after continuing from a frozen stage-one hidden state. Fix the *ground-truth target digit* \(y\) and a competing digit \(c_T\ne y\) selected from the **clean** output. Define the scalar target margin
\[
m_T(h)=(e_y-e_{c_T})^\top F_T(h).
\]
Using the target digit is permitted only for evaluation; no held-out target is used to fit the SAE, feature correspondence, or orientation.

For an exact unit hidden-space direction \(u\), define the symmetric finite-radius response at amplitude \(r>0\):
\[
\boxed{D_r m_T(h,u)=\frac{m_T(h+ru)-m_T(h-ru)}{2r}.}\tag{1}
\]
Both endpoints are evaluated with the *same* teacher checkpoint and the same fixed competitor digit \(c_T\).

**Theorem OLM-14B (finite-radius causal transfer bound).** Suppose \(m_A,m_B\) are twice differentiable on the two declared intervention line segments, with Hessian bilinear operator norm bounds \(M_A,M_B\). Let \(u_A,u_B\) be unit directions, \(s\in\{-1,+1\}\) a sign fixed from calibration only, and \(\alpha\ge0\). If
\[
\left|D m_B(h_B)[u_B]-s\alpha\,D m_A(h_A)[u_A]\right|\le\varepsilon,
\]
then
\[
\boxed{\left|D_r m_B(h_B,u_B)-s\alpha D_r m_A(h_A,u_A)\right|
\le\varepsilon+\frac r2(M_B+\alpha M_A).}\tag{2}
\]

**Proof.** Taylor expansion at the positive and negative line endpoints gives
\[
m(h\pm ru)=m(h)\pm rDm(h)[u]+R_\pm,\qquad |R_\pm|\le Mr^2/2.
\]
Subtracting the expansions and dividing by \(2r\) yields \(|D_r m-Dm(h)[u]|\le Mr/2\). Apply the triangle inequality to both teachers, with the calibration-fixed orientation \(s\) and scale \(\alpha\). QED.

A valid instance of (2) needs independently verified Hessian bounds and a derivative-alignment premise. SMC-14 measures finite differences, not a certificate for this bound. Its source-locked output should report a statistical transfer score separately from any rigorous local recurrent certificate.

## 3. A sufficient exact causal intertwiner

**Theorem OLM-14C (isometric signed causal conjugacy).** Suppose an isometric linear map \(P\) relates the two 48-dimensional goal-token state spaces, \(h_B=Ph_A\), and the frozen task-margin maps obey
\[
m_B(Px)=\alpha m_A(x)+\beta,\qquad \alpha>0
\]
at all points in both intervention segments. If a matched target decoder direction is \(u_B=sPu_A\), with \(s=\pm1\), then
\[
\boxed{D_r m_B(h_B,u_B)=s\alpha\,D_r m_A(h_A,u_A)}.
\]
**Proof.** Evaluate the assumed equality at the positive and negative endpoints, using linearity and \(P(h_A\pm sru_A)=h_B\pm ru_B\), subtract, and divide by \(2r\). The additive offset cancels. QED.

This is a sufficient condition for signed transfer, not an assumption that activation cooccurrence discovers such a map. Feature labels can be arbitrarily permuted while all physical statements remain unchanged, provided assignment and decoder coordinates are permuted consistently.

## 4. Puzzle-clustered centered causal scores

For each independently generated test puzzle \(p\), choose a fixed \(k\ge2\) of its missing goal tokens using the visible blank pattern. Evaluate two response vectors \(a_p,b_p\in\mathbb R^k\), with \(b_p\) corresponding to a calibration-frozen feature mapping. Put
\[
P_k=I_k-\frac1k\mathbf 1\mathbf 1^\top,\quad
C_p(a,b)=\frac{\langle P_ka,P_kb\rangle}{\|P_ka\|_2\|P_kb\|_2}
\tag{3}
\]
when both centered norms are strictly positive. A zero norm causes a declared abstention.

**Theorem OLM-14D (puzzle nuisance removal).** For arbitrary puzzle-specific constants \(c_p,d_p\), and positive scales \(s,t>0\),
\[
\boxed{C_p(sa+c_p\mathbf1,tb+d_p\mathbf1)=C_p(a,b).}
\]
**Proof.** \(P_k\mathbf 1=0\), so the nuisance constants vanish and positive scales cancel from the normalized inner product. QED.

This measure removes *puzzle-level constant* shifts and positive scale differences. It cannot remove arbitrary token-position patterns, common Sudoku target-digit effects, or nonlinear teacher capability mismatch. Those require explicit held-out negative controls.

## 5. Calibration-only orientation and correctly matched nulls

Let \(\pi\) be the 96-feature one-to-one permutation fit using **only the existing SMC-13 64-puzzle calibration cohort**, with position-and-visible-input-digit-conditioned coactivation. Let \(\pi_{\mathrm{shuffle}}\) be fit from target vectors shuffled within exactly those visible groups. Both assignments and their SHA-256 fingerprints are frozen before the test puzzle families are evaluated.

For each assignment and teacher pair, choose a *single global orientation*
\[
s_\pi=\begin{cases}
+1&\sum_{p\in \mathrm{calib}}\langle P_k a_p,P_k b_{p,\pi}\rangle\ge0,\\
-1&\text{otherwise}.
\end{cases}\tag{4}
\]
Use the same rule to orient the shuffled and random assignment controls. Never change the sign in response to held-out outcomes.

**OLM-14E (label and sign gauge).** If both feature dictionaries are relabeled by permutations \(\sigma_A,\sigma_B\) and the assignment becomes \(\sigma_B\circ\pi\circ\sigma_A^{-1}\), while their physical decoder columns are relabeled accordingly, every causal endpoint and the centered response score remain the same. The orientation choice (4) is also invariant under this relabeling.

This observation clarifies the scientific hypothesis. A *positive held-out transfer-minus-null result*, with puzzle-clustered uncertainty, may show that the **specific calibration-frozen feature correspondence** predicts transferable causal behavior beyond the chosen negative controls. It does not identify a unique semantic circuit, guarantee a shared latent basis, or establish transfer of capability between checkpoints with very different task accuracies.

## 6. Registered applied falsification protocol

The SMC-14 implementation uses the fixed original pretrained teacher A and the independently trained teachers B501 and B701 from SMC-13, with both SAE seeds per new teacher. It uses exactly the same 64 distinct source calibration puzzles, frozen SMC-13C assignment recipe and its within-position/input-digit shuffled pairing. Then it tests on **three separate 64-puzzle solution cohorts**: structurally novel 30-hole puzzles, novel 34-hole puzzles, and canonical 30-hole controls. At each puzzle, a deterministic set of eight evenly spaced missing cells is selected using the *visible mask alone*. The target digits enter only the final margin-effect evaluation.

The finite intervention radius is fixed at \(r=0.2\) in physical hidden-state L2 norm, using an FP64 three-step continuation after the FP32 stage-one source anchor. Report both raw and orientation-calibrated within-puzzle signed causal correlation, original teacher/target teacher clean task accuracy, and matched-control paired differences. Controls include the calibration-frozen clue-conditioned shuffled feature assignment, a seeded random feature assignment, and within-puzzle goal-response shuffling. The benchmark resamples 64 independent puzzle IDs rather than individual token observations.

The **primary null gate** tests whether the orientation-calibrated mean within-puzzle causal cosine for the frozen clue-conditioned matching exceeds the strongest predeclared mapping-null mean on novel30 **and** novel34 tests, with a descriptive 95% puzzle bootstrap paired-difference interval above zero. The confidence intervals are descriptive over these deterministic seeded cohorts; repeated comparison across many teacher pairs does not make a population-significance claim.

A null result or an advantage only over one weak control will be retained. Where the newly trained teachers are substantially less capable than the original pretrained teacher, causal agreement is not evidence that the same level of Sudoku reasoning has transferred.

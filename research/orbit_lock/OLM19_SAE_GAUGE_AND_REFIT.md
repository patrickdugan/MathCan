# OLM-19: Orthogonal transport, exact SAE reconstruction aliases and finite causal feature stability

November 16, 2026. Mathematical companion to the [prospectively frozen SMC-19 independent SAE-refit study](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/smc19-sae-refit-gauge-20261116/research/real_recurrence_sae_v1/SMC19_PROTOCOL.md). Extends the OLM-14–18 causal-observer line. These finite-dimensional statements use classical linear algebra and Lipschitz bounds in a new experimental contract. Priority beyond the explicit constructions is not asserted. Proofs are written here and supported by exact \`fractions.Fraction\` witnesses; there is **no Lean kernel formalization** in this PR.

## OLM-19A. Exact joint hidden-state gauge conjugacy

Let \(h\in\mathbb R^d\) denote a *row* hidden vector, \(Q\in O(d)\) a fixed orthogonal matrix, \(T:\mathbb R^{n\times d}\to\mathbb R^{n\times d}\) a frozen tied recurrent step and \(H:\mathbb R^{n\times d}\to\mathbb R^{n\times c}\) its output head. Define the conjugated functions

\[
T_Q(v)=T(vQ^\top)Q,\qquad H_Q(v)=H(vQ^\top).
\]

For a frozen top-k SAE physical feature code \(z(h)\), decoder columns \(d_i\) and SAE reconstruction \(R(h)=b+\sum_i z_i(h)d_i\), set \(z_Q(v)=z(vQ^\top)\), \(d_{Q,i}=d_iQ\) and \(R_Q(v)=R(vQ^\top)Q\).

**Theorem OLM-19A.** For every integer \(L\ge0\), every initial hidden state \(h\), every feature index \(i\), and every finite native decoder-contribution edit \(\delta_i=z_i(h)d_i\),

\[
\boxed{T_Q^{\,L}(hQ)=T^{\,L}(h)Q,\quad
 H_Q(T_Q^{\,L}(hQ))=H(T^{\,L}(h)),}
\]
\[
\boxed{z_Q(hQ)=z(h),\quad R_Q(hQ)=R(h)Q,\quad
 \|\delta_iQ\|_2=\|\delta_i\|_2,}
\]
and the output margin from editing \(hQ\) by \(\delta_iQ\) agrees **exactly** with that from editing \(h\) by \(\delta_i\) before \(L\) original recurrent steps. This holds for arbitrary nonlinear tied \(T\) and nonsmooth top-k code \(z\).

**Proof.** Since \(Q^\top Q=I\), the first recurrence identity holds for \(L=0\). If it holds for \(L\), then \(T_Q(T^{\,L}(h)Q)=T(T^{\,L}(h)QQ^\top)Q=T^{\,L+1}(h)Q\); induction proves all \(L\). Substituting into \(H_Q\) proves output identity. The SAE equalities follow directly from its definition under the coordinate adapter, without differentiability. Orthogonal maps preserve physical L2 norms. Finally, \((hQ-\delta_iQ)Q^\top=h-\delta_i\), so the same recurrence/head identity applies to edited trajectories. QED.

Under an arbitrary invertible \(P\in GL(d)\), the conjugacy equalities still hold after consistent coordinate changes, although an L2 dose-matched control is generally **not** invariant. Orthogonality is the experimental control because SMC-19 fixes original physical L2 intervention doses.

**Scope:** SMC-19's rotated SAE is transported *without independently fitting new weights*. Passing this theorem's numerical regression checks a software implementation and numerical precision. It does not establish that independently trained dictionaries recover the same features.

## OLM-19B. Perfect SAE reconstruction and identical matched activations can hide opposite native causal signs

Consider physical hidden states \((x,y)\) in the positive quadrant \(x>0,y>0\). Define two ReLU autoencoders with active two-coordinate codes and linear physical decoders:

\[
z_A(x,y)=(x,y),\qquad d^A_1=(1,0),\quad d^A_2=(0,1),
\]
\[
z_B(x,y)=(x+y,y),\qquad d^B_1=(1,0),\quad d^B_2=(-1,1).
\]

Both have **zero reconstruction error** on the entire quadrant:
\[
\boxed{z_A^1 d^A_1+z_A^2 d^A_2=(x,y)
       =z_B^1d^B_1+z_B^2d^B_2.}
\]
Their second atom has exactly identical activation on every input: \(z_A^2=z_B^2=y\). All indicated ReLU coordinates are positive and can be embedded in larger top-k SAE widths by adding dormant atoms.

Fix a *single unchanged task teacher* with target digit margin \(m(x,y)=10+2x+y>0\) for the clean positive quadrant. Erase the native contribution of that matched second atom, separately for the two SAE decompositions. This yields
\[
h-\delta_A=(x,0),\qquad h-\delta_B=(x+y,0).
\]
Consequently
\[
\boxed{m(h)-m(h-\delta_A)=+y,\qquad
       m(h)-m(h-\delta_B)=-y.}
\]

**Theorem OLM-19B.** Even identical matched feature activations on **every** natural input, exact full hidden-state reconstruction by both dictionaries, and the same clean task output on one unchanged teacher cannot determine the sign of the matched native feature's causal erasure effect.

**Proof.** Both reconstruction equalities hold by substitution, and the matched second codes are the common scalar y. The target margin differences calculate to +y and −y, strictly opposite for every y>0. No coordinate difference in the frozen task teacher, no approximation and no changed task label is involved. QED.

This witness is relevant to SMC-19 because an SAE learned again from the same teacher's states may reconstruct them equally well yet attribute portions of the hidden state to incompatible decoder columns. Calibration-only Hungarian coactivation matching is insufficient for an identity theorem. A positive empirical native-causal transfer advantage must therefore be interpreted *under the specific trained dictionaries and nulls*.

## OLM-19C. A sharp sufficient physical-edit stability bound

For a common clean state h and differentiable frozen task margin \(m\), let two SAE features induce physical erasures \(\delta_A=z^A_i d^A_i\) and \(\delta_B=z^B_j d^B_j\). Assume \(\|\nabla m(x)\|_2\le L\) along the complete straight segment connecting \(h-\delta_A\) and \(h-\delta_B\). Let \(E_A=m(h)-m(h-\delta_A)\), \(E_B=m(h)-m(h-\delta_B)\).

**Theorem OLM-19C.**
\[
\boxed{|E_A-E_B|\le L\,\|\delta_A-\delta_B\|_2.}\tag{1}
\]

If \(|E_A|>L\|\delta_A-\delta_B\|_2\), the sign of \(E_B\) must equal that of \(E_A\), and \(E_B\) is nonzero. Thus sufficiently close *physical decoded contributions* are a mathematical sufficient condition for the observed causal erasure sign to transfer under a fixed teacher.

**Proof.** Parameterize the line from \(h-\delta_A\) to \(h-\delta_B\) and apply the fundamental theorem of calculus. The derivative along the line is bounded by \(L\|\delta_A-\delta_B\|_2\); integration yields (1). If \(E_B\) had opposite sign or zero, then \(|E_A-E_B|\ge|E_A|\), contradicting the strict premise. QED.

The coefficient is sharp: for linear \(m(x)=10+3x_1+4x_2\), whose gradient norm is 5, choose \(\delta_A=0\), \(\delta_B=(3/5,4/5)\). The absolute effect difference is exactly 5, the edit distance is exactly 1, and equality holds. For a fixed physical dose r with \(\|\delta_A\|=\|\delta_B\|=r\), the difference is also controlled by the decoder angle:
\[
\|\delta_A-\delta_B\|_2^2=2r^2(1-\cos\theta),
\]
where \(\theta\) is the angle between the actual physical edit vectors, not merely their SAE activation codes. This gives a concrete future measurable sufficient-condition card for refit stability.

## OLM-19D. Frozen matched-control statistics are equivariant under a consistent orthogonal gauge

The SMC-19 primary outcome combines signed target-margin losses \(E_{\mathrm{reference}}\), \(E_{\mathrm{mapped}}\), \(E_{\mathrm{other}}\) from identical input puzzles, with two global orientation signs fitted on a separate calibration cohort and paired puzzle-cluster bootstrap. Apply a *single common* orthogonal hidden-coordinate gauge Q to the teacher, both dictionaries, all physical intervention vectors and their source states, and carry the original frozen feature assignment and deterministic control choices along unchanged.

**Proposition OLM-19D.** Every original causal margin loss, calibration orientation product, eligible-feature activation flag, signed concordance score, and resulting puzzle-bootstrap statistic remains identical in exact arithmetic under the joint transported representation.

**Proof.** By OLM-19A, the codes and all three output margin losses are identical. A bijective feature relabeling carried consistently with the dictionaries/assignment preserves those values. The calibration products, sign choices and per-puzzle score arithmetic are then unchanged, so every deterministic resample of puzzle IDs has the same value. QED.

If instead one retrains an SAE with a new random seed after rotating the data, the hypothesis of a joint transported dictionary fails. Even a label-permutation control requires its permutation to be transported consistently; a Hungarian solver's arbitrary tie-breaking among equal-optimum assignments is an additional implementation gauge.

## Experimental contract and interpretation

SMC-19 independently refits new SAE seeds 131/167 on exactly the original frozen B501/B701 teacher training and validation hidden states, freezes checkpoints and observed-clue-conditioned Hungarian matching on the original calibration cohort, then compares their *naturally active* native decoder contribution erasures against equal-dose other-active controls on two fresh noncanonical Sudoku cohorts. A separate exact orthogonal basis transport sanity test uses original trained SAE71/teacher weights and cannot be counted as an independent refit.

The results can test a conditional *operational feature-transfer stability hypothesis*. Even a positive empirical score will not establish an intrinsic semantic SAE atom, because the explicit OLM-19B reconstruction-equivalent alias and the OLM-18 inactive-gradient dual gauge make that conclusion underdetermined. No new Lean statements are claimed verified; the exact rational witnesses in this PR check the algebra on bounded examples.

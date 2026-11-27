# Pre-proposal causal exposure and orthogonal dictionary gauge

ALG-DESCENT-08 companion; elementary identities for a fixed recurrent router. See DataGoblin PR #89.

Let h_0 be independent of W, h_{t+1}=tanh(b_t+W h_t), with prescribed inputs b_t. For a physical matrix edit E, use W+epsilon E and the same inputs. The derivative z_t at epsilon=0 satisfies z_0=0 and
    z_{t+1}=D_t(W z_t+E h_t),
where D_t=diag(1-tanh(b_t+W h_t)^2). By induction,
    z_T=sum_{t=0}^{T-1} (D_{T-1}W)...(D_{t+1}W) D_t E h_t
with the empty product identity. A zero initial state implies the first-pass edit has zero direct effect; a nonzero state gives an opportunity for an edit when E h_0 !=0. It does not guarantee nonzero final logit effect or changed discrete action. Distinct passes can cancel and readouts can annihilate the perturbation.

For finite edit E, componentwise tanh is 1-Lipschitz in Euclidean norm, so
    ||h'_{t+1}-h_{t+1}|| <= ||W|| ||h'_t-h_t|| + ||E h'_t||.
This depends on edited states. Matching clean calibration RMS of E h_t does not match downstream transport, edited-state writes, or held-out distributions. It is therefore a weak calibration control rather than a causal equivalence. The derivative identity motivates readout-Jacobian matched shams with prospectively fixed calibration and OOD mismatch reporting.

For real skew-symmetric K, Q=exp(K) is orthogonal: Q^T=exp(-K), Q^TQ=I. For W=AB and square orthogonal Q, (AQ)(Q^TB)=W, so the sum of rank-one column/row atoms is invariant while their individual writes may change. Behavioral reconstruction/sparsity can select a basis but does not imply uniqueness. Compare learned rotation to SVD and random rotation bases under equal atom-selection budgets before attributing a mechanism to the learned decomposition. These are paper proofs; no Lean verification performed.
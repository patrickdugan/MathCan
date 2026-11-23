# RH-26B-02 — theta integration and archimedean quotient conditions

**Date:** 2026-11-23  
**Upstream:** `leanprover-community/riemann-hypothesis@c900e67c2fcd1fdb041685820bbd2b867fbc5a4b` (pinned; main confirmed unchanged at read time).  
**MathCan:** `research/rh26-extraction-rubrics-20261123`, draft PR #265.  
**Result:** **PARTIAL SOURCE PASS** for concrete theta operator and quotient/interface constraints; **BLOCKED** on locating original `WeilTensorModels.ThetaIntegralsAgree` and `WeilTensorModels.LocalMatching` declarations. **No independent Lean check**.

## Scope and inspection receipt

One upstream file read: `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean`, lines **251–500 inclusive**, 250 source lines. This continues after RH-26B-01, which read lines 1–250 in an earlier run. There were no reads beyond line 500 and no repository-wide scan. The full file is intentionally not loaded into context. The original premise definitions were **not located in this window**.

## 1. The operator is a real integral, with normalization dependencies

The source defines a Weil-like representation
`Rep σ X W := UA σ X.J × UA σ W.J →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)`
at [WeilTensorModels.lean:L251–L253](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L251-L253), and then defines

```text
theta om Φ g h = thetaSum F (om (g,h) Φ)
Model.I M om Φ h = ∫ g in M.dom, theta om Φ g h ∂M.μ
Model.Conv M om Φ = ∀ h, IntegrableOn (fun g => theta om Φ g h) M.dom M.μ
```

See [WeilTensorModels.lean:L319–L330](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L319-L330). `Model.IsGood` requires a Haar measure `M.μ`, a fundamental domain `M.dom` for the rational subgroup, and nontrivial local vacuum/standard-vector conditions ([WeilTensorModels.lean:L269–L279](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L269-L279)). Thus the concrete comparison needs more than an algebraic bilinear map: measure, fundamental-domain choice, convergence, and the representation action all matter.

A candidate operator compression may only replace `I` when it preserves the relevant choice of `M.μ`, convergence for the tested functions, and the appropriate invariance/equivariance hypotheses. A matched scalar may depend on normalizations; the window supplies no formula for it.

## 2. Geometric admissibility is restrictive

The `Geo` structure stores a pair of spaces, their joint space, and two Weil models ([WeilTensorModels.lean:L351–L365](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L351-L365)). `Geo.IsGood` requires `a' < a`, parity of `a + a'`, two explicit rank gaps `2(p+q)+1 < (a-a')/2` and `2(p+q)+1 < a'`, correct Hermitian/skew-Hermitian signatures, and good Weil models ([WeilTensorModels.lean:L396–L408](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L396-L408)).

A separate `Chars.IsGood` adds Hecke-character and local ramification assumptions ([WeilTensorModels.lean:L412–L424](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L412-L424)). `IsTriple` then combines these with the Weil-model inputs ([WeilTensorModels.lean:L426–L431](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L426-L431)). Any finite-dimensional analogy omitting these is a **TOY**, with no implication about the automorphic proof.

## 3. A quotient representation with infinitesimal and compact constraints

At [WeilTensorModels.lean:L434–L455](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L434-L455), `RealMaps` stores a complex module `Pi` and two linear maps `p,p'` from the relevant Schwartz spaces into `Pi`. `FinMaps` stores corresponding prime-indexed local maps.

Given a model `M`, the structure `RealQuot B M om p` demands the following at [WeilTensorModels.lean:L463–L469](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L463-L469):

- **Onto from polynomial vectors:** the image under `p` of the selected polynomial submodule `M.Pol` is the entire target `Pi`.
- **Lie annihilation:** for allowable one-parameter subgroup derivatives `f₁`, `p f₁ = 0`.
- **Compact invariance:** for allowable compact-group actions `f ↦ f₁`, `p f₁ = p f`.

The paired `IsRealMaps` structure requires both quotients, compatibility of their images under the **other** group's Lie derivatives and compact actions, nontriviality of `Pi`, and irreducibility of the common image against the indicated Lie/compact stability conditions ([WeilTensorModels.lean:L471–L484](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L471-L484)).

This pinpoints the operator-theoretic obstacle: the correct reduced object is a representation-sensitive quotient or coinvariant with a joint image, not merely the vector space of integrand values.

## 4. Local comparison gate already present

`IsZetaAt` at [WeilTensorModels.lean:L486–L494](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L486-L494) requires local linear-model isomorphisms, specific standard-vacuum indicator functions, and an equivalence between equality of the local quotient images and equality of two explicitly different local transforms, `bigP` and `smallP`. The precise definitions and normalizations of those transforms were not reached in this pass. `IsFinMaps` begins at [WeilTensorModels.lean:L496–L500](https://github.com/leanprover-community/riemann-hypothesis/blob/c900e67c2fcd1fdb041685820bbd2b867fbc5a4b/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L496-L500) and continues beyond the inspection boundary; its complete constraints are not yet known.

## 5. Compression theorem candidate for MathCan (not checked)

A minimal independent **linear-algebra lemma** could be:

For a complex vector space `S`, a subspace `K` generated by specified infinitesimal-action images and compact-action differences, and a linear map `p : S →ₗ[ℂ] Pi`, if `K ≤ ker p` then there is a unique induced linear map `S ⧸ K →ₗ[ℂ] Pi`. If `p` is surjective, the induced map is surjective. This is the standard quotient universal property and can be independently proved under MathCan's pinned Lean version.

That result would establish only the algebraic quotient step. To use it in the RH chain, a separate analytic proof must show the actual theta-integral operator annihilates `K` under the stated convergence hypotheses. The quotient must also support the paired image and irreducibility requirements found above.

**Falsifier:** if the theta integral fails to descend to the proposed coinvariant quotient, or the quotient omits one of the Lie/compact matching constraints, a proposed replacement cannot inherit the `RealQuot` and `IsRealMaps` inputs.

## Next bounded extraction

**RH-26B-03:** continue **only** the pinned source file `WeilTensorModels.lean` at **lines 501–750**, using at most one 250-line window. Look for the original `WeilTensorModels.ThetaIntegralsAgree` and `WeilTensorModels.LocalMatching` declarations; otherwise record the next exact range. Prioritize their signatures and immediate hypotheses. Do not infer that they lie in any particular following window. Keep the usual eight-file / 1,200-line / two-hop cap.

**Resource receipt:** targeted GitHub connector read only; no Lean build, no CI job, no GPU/QPU/cloud usage. RAM and wall time unmeasured.

# RAM-14: Structural Lean tactic coverage at the GramianTransfer boundary

**Date:** 16 November 2026  
**Classification:** Retrospective diagnostic on previously failed, publicly inspected RAM-13 theorems  
**Trust:** Source-exact Lean 4.35 full-theorem proof, two original compiles plus independent third replay

## Result

The registered RAM-13 neural and symbolic policies each failed to certify two new-source GramianTransfer theorems within the original search budget. RAM-14 isolates a **tactic-generator coverage deficiency** using a new posthoc, source-header-only grammar. Its generator reads the target statement and earlier source declaration headers. It has no access to the target's original reference proof when making candidates.

The public [first native CI run #43791363290](https://github.com/patrickdugan/MathCan/actions/runs/43791363290) generated 35 candidates. Exactly four certified entire original target statements by **two** separate Lean4.35 compilations, including the original `#print axioms` gate. A distinct [third-compilation audit #43791713791](https://github.com/patrickdugan/MathCan/actions/runs/43791713791) reconstructed every original candidate from source, checked original logs and bytes, and **independently compiled all four accepted proofs a third time**.

| Previously failed theorem | Generated candidate scripts | Three-times compiled proof variants |
|---|---:|---:|
| `MathCan.GramianTransfer.transport_iterate` | 15 | 1 |
| `MathCan.GramianTransfer.observable_transport` | 20 | 3 |
| **Total** | **35** | **4** |

Every success had the sole transitive axiom `propext`, with zero false certificates and zero timeouts. The other 31 candidates were compiler-rejected; their original sources and logs are retained in the archived evidence.

## Two successful algorithms

**Typed natural-number induction:**

```lean
induction n generalizing x <;>
  simp_all [iterateState, transport, g.left_inv]
```

This source-generated one-shot tactic proved **both** original theorems. The generator selects `n : Nat`, `x : α`, the preceding definitions `iterateState` and `transport`, and the prior structure field `StateGauge.left_inv` through the binder `g`. It does not copy the original proof commands.

**Earlier-theorem rewriting:**

```lean
simp [transport_iterate, g.left_inv]
```

This proves `observable_transport`. The same result was obtained with `simpa [transport_iterate, g.left_inv]`. The `transport_iterate` lemma was declared before the target theorem, and its **statement**, not its proof body, was the source-selection signal.

The original 20-family RAM-08 grammar creates `induction_list` candidates for list-valued local binders and `rw_local` for local hypotheses. The new `Nat` induction and earlier-lemma rewrite rules address missing *source-visible action families*. This is a concrete coverage explanation of a historical failure; the original RAM-13 search outcomes and metric remain unchanged.

## Mathematical normal form

For a bijective state coordinate map `g`, define the transported update `T_g = g ∘ f ∘ g⁻¹`. The original source identities are

\[
T_g^n(g(x)) = g(f^n(x)), \qquad
\rho(g^{-1}(T_g^n(g(x)))) = \rho(f^n(x)).
\]

The first follows by induction on `n`, generalizing `x` so the induction hypothesis is available after one update `f(x)`. The second follows from the earlier transport identity and the inverse law. These are established original MathCan statements, and the RAM-14 contribution is an auditable **tactic-generation mechanism**, not a claim of a new theorem.

## Audit ledger and limitations

- Frozen first source: `MathCan@f427e0ef4a61093304d12ca2c0dc943d8d2429e5`, original file Git blob `f07e99a3f27acba22c2c0c6b3f675a68ab774ab2`.
- Original failure baseline: [RAM-13 PR #105](https://github.com/MoralityLabAI/LoopedTransformers/pull/105), 0/2 for all original policies in the fixed fresh cohort.
- [Posthoc protocol](PROTOCOL.md) committed at `40e7c63` before the source-only CI diagnostic. The target proof bodies and previous RAM-13 failure were already visible before protocol registration.
- [First native run #43791363290](https://github.com/patrickdugan/MathCan/actions/runs/43791363290), artifact `ram14-posthoc-structural-grammar-43791363290`, artifact ID `14192616133`; 35 attempts, four double-compiled.
- [Independent third audit #43791713791](https://github.com/patrickdugan/MathCan/actions/runs/43791713791), artifact ID `14192592821`; all 35 inputs reconstructed, all four accepted sources triple-compiled, original case-receipt SHA256 `5fafd892b040ca5bc73d20002516fd45cf0a8f5409ff370590a1699c041fe0df`.
- Eight Python source-isolation and grammar tests passed. The very first run failed a parser contract on Unicode type binder `α`; [the corrected run](https://github.com/patrickdugan/MathCan/actions/runs/43791363290) and independent audit passed, preserving the failed run as engineering history.

**Important:** These two theorem roots were selected *after* an unsuccessful prospective run and their original public source proofs were inspected. RAM-14's one-shot macro candidates are not matched to the original recurrent/flat full-search budget or architecture. **No prospective model capability gain is claimed.** Native proof success is genuine for these original theorem statements and extends the auditable grammar evidence.

## Reproduce

```bash
python -m unittest discover -s research/ram14 -p 'test_grammar.py' -v

# mathcan-pinned is a separate checkout at the exact old source commit
(cd mathcan-pinned && lake build MathCan)

python research/ram14/diagnose.py \
  --mathcan mathcan-pinned --out /tmp/ram14-first

# A separate job retrieves immutable first-run artifact run 43791363290
python research/ram14/independent_audit.py \
  --mathcan mathcan-pinned \
  --first-artifact /tmp/first-run-extracted \
  --out /tmp/ram14-third
```

The paper direction for RAM-15 is a **fresh, preregistered source-family evaluation** that keeps the expanded grammar identical across neural and symbolic controllers, controls the extra candidate budget, and uses entirely unopened theorem roots. The registered RAM-08 PEF and RAM-10 original evaluation questions remain separate.

# BSAR-09: exact finite-product certificates and a rational-window RLT gym

The [original BSA-R Step 7 source](https://github.com/VivienSweetbrier/bsa-r/blob/80c62433b0eb671175bd8d6169822d3ebd922b60/lean/Step7VorticityDirectionPdeRound6.lean) proves a finite-window doubling bound from local arithmetic constraints. MathCan's [BSAR-08](https://github.com/patrickdugan/MathCan/pull/184) tightened the local result to a dimensionless-cost envelope.

This package converts that envelope into a **finite-product certificate** and creates paired, independently checked rational examples for a recurrent proof-scope model. It stays within MathCan's pinned Lean 4.35.0, Init-only project.

## Exact Lean certificate

For each of `K` windows, assume fixed integer `M > 0`, `I_m >= 0`, `d_{m+1} >= 0`, `2 I_m <= M`, and

```text
M * (d_(m+1) - d_m) <= I_m * d_(m+1).
```

The previously verified local theorem gives:

```text
M * d_(m+1) <= (M + 2 I_m) * d_m.
```

The new [`MathCan/BSARFiniteProduct.lean`](../../MathCan/BSARFiniteProduct.lean) defines an inductive `RatioProductChain` that records the exact numerator and denominator

```text
denom_K = product over m<K of M
numer_K = product over m<K of (M + 2 I_m).
```

Its kernel-checkable conclusion is

```text
denom_K > 0
numer_K >= 0
denom_K * d_K <= numer_K * d_0
```

for every **finite** `K`. A separate `budgeted_cross_multiplied` lemma shows that a *supplied* product cap `numer_K <= budget * denom_K` gives a corresponding endpoint cap.

Because the proof tracks integer products, it supports exact rational interpretation without floating point. **A horizon-independent bound has not been derived from the original local premises.** That requires a uniform aggregate constraint on `sum(I_m/M)` as discussed in [BSAR-09 issue #186](https://github.com/patrickdugan/MathCan/issues/186).

## Exact Fraction challenge set

The [`scripts/bsar09_exact_oracle.py`](../../scripts/bsar09_exact_oracle.py) generates paired positive/negative sequences with Python's standard-library `fractions.Fraction`, including exact rational states. Each positive case saturates the original ODE at all windows:

```text
d_(m+1) = (M / (M - I_m)) * d_m.
```

Its negative partner preserves the prefix and perturbs the last endpoint halfway between the **tight source-ODE limit** and the **weaker BSAR-08 envelope**. Therefore each negative case violates exactly one source-ODE condition while still satisfying the finite product bound.

This deliberately prevents a model from substituting the easier product test for checking all original source assumptions.

| Split | Cases | Matched pairs | Parameter regime |
|---|---:|---:|---|
| Train | 256 | 128 | `M=4,6,8,10`, `K=1..4` |
| Development | 64 | 32 | `M=12,14`, `K=5..6` |
| Test | 144 | 72 | `M=16,18,20`, `K=7..9` |
| **Total** | **464** | **232** | Disjoint integer `M` and length ranges |

The constant-answer baseline is exactly **50% example accuracy** and completes **zero matched pairs**. The exact Fraction verifier is the label oracle, not a trained-model result.

```sh
python -m unittest discover -s tests -p 'test_bsar09_exact_oracle.py' -v
python scripts/bsar09_exact_oracle.py generate --output-dir /tmp/bsar09
python scripts/bsar09_exact_oracle.py audit --corpus /tmp/bsar09/corpus.jsonl
python scripts/bsar09_exact_oracle.py score \
  --corpus /tmp/bsar09/corpus.jsonl \
  --predictions /tmp/bsar09/model_predictions.jsonl
```

The `public_test.jsonl` file strips gold labels and oracle traces from model inputs. The source JSONL is public, so users must audit training contamination before treating these examples as unseen to a pretrained model. The manifest binds all files to SHA-256 hashes, the source commit, and a deterministic seed.

## Mathematical next step

With `a_m = I_m/M` and `0 <= a_m <= 1/2`, the local bound can be read as

\[
D_{m+1}\leq(1+2a_m)D_m.
\]

Consequently,

\[
D_K\leq D_0\prod_{m<K}(1+2a_m)
\leq D_0\exp\left(2\sum_{m<K}a_m\right).
\]

The finite integer cross-product implication is formalized in this PR. The **real-valued exponential inequality** is a standard analytic fact stated here for the next separate proof. Its use near a possible Navier–Stokes singularity requires the additional estimate

\[
\sup_{K}\sum_{m<K}\frac{I_m}{M}<\infty.
\]

At present there is no verified PDE theorem supplying that uniform budget or connecting these abstract windows to actual smooth solutions. Direction-cone regularity and the physical definition of `I_m` remain open. The construction here is an arithmetic consistency check, with no fluid solver or global-regularity claim.

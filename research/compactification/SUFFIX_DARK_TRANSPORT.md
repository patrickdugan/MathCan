# NRF-08: suffix transport of dark-to-observed Jacobians

Date: 2026-11-15. Exact finite-dimensional identity, norm bounds and exact rational checks. This is a research-program synthesis of standard block operator algebra, **not a worldwide mathematical-priority claim**.

## Exact composition theorem

Fix a point h in a differentiable tied recurrent map F, and an orthogonal observation projector P of rank k>0; put Q=I-P. Let T_s=D(F^s)(h) be the tangent over the first s visits and let S_u=D(F^u)(F^s(h)) be the tangent over the next u visits. The chain rule gives T_{s+u}=S_u T_s.

Define C_s=P T_s Q, D_s=Q T_s Q, A_u=P S_u P, and B_u=P S_u Q. Since P+Q=I,

```
C_(s+u) = A_u C_s + B_u D_s.
```

The first summand carries forward leakage already visible at depth s. The second injects dark-sector tangent influence through the additional visits. The exact energy identity is

```
||C_(s+u)||_F² = ||A_u C_s||_F² + ||B_u D_s||_F²
                  + 2 <A_u C_s, B_u D_s>_F.
```

For L_s=||C_s||_F/sqrt(k), triangle and reverse-triangle inequalities yield

```
max(0, ||B_u D_s||_F/sqrt(k) - ||A_u||_op L_s)
 ≤ L_(s+u)
 ≤ ||A_u||_op L_s + ||B_u D_s||_F/sqrt(k).
```

A sufficient condition for a **strict leakage increase** is

```
||B_u D_s||_F/sqrt(k) > (1+||A_u||_op) L_s.
```

The condition is sufficient rather than necessary, because the Frobenius cross term may be constructive. If D F(h_i)=I+E_i, then for arbitrary noncommuting steps

```
L_s ≤ ||T_s-I||_op ≤ product_(i=0)^(s-1) (1+||E_i||_op) - 1.
```

The second inequality follows by expanding the ordered product as a sum of nonempty ordered words and applying submultiplicativity. For a tanh residual F(h)=h+β(W₂ tanh(W₁h+b₁)+b₂), each ||E_i||_op ≤ |β| ||W₂||_op ||W₁||_op. The resulting bound is uniform, often loose, and yields no positive lower bound on leakage.

### Counterexamples and Jordan specialization

For J=[[1,b],[0,1]] and coordinate P=diag(1,0), first-s and next-u shears give C_s=sb E12, A_u C_s=sb E12 and B_u D_s=ub E12. The cross term is 2sub², and L_(s+u)=|s+u||b|. A 90-degree planar rotation has L_1=1 and L_2=0 for that P, establishing that longer depth alone does not imply larger leakage.

## Connection to NRF-08X

The preregistered NRF-08 strict checkpoint byte gate failed: locally regenerated PyTorch .pt SHA-256 hashes differ from the original NRF-07 archived hashes. The exact same source-compatible training algorithm reproduced the six original-suffix metrics within 5e-15, but **byte-identity is unverified**. The subsequent fixed-state suffix study is labeled NRF-08X exploratory.

With trained weights, decoder basis and midpoint states fixed, the source-compatible reproduction lengthens the suffix from 8 to 16 visits. For the three R32-trained models, the supervised-minus-random-median objective at lambda=1 changes from negative at suffix 8 to positive at suffix 16, in 3/3 reconstructed models. All six models gain supervised leakage.

An independent 128x128 full-Jacobian multiplication decomposed the measured leakage. The cross term between advected leakage and new dark injection was positive on all 72 shadow states (six reconstructed model checkpoints times 12 shadow states). This supports a mechanism involving constructive transport and injection within this small signed-permutation toy family. See the NRF-08X report and compact receipts in LoopedTransformers PR #56. Full original binary identity and external architectural generality remain open.

## Checks and formal scope

- `suffix_leakage_transport.py` uses Fraction to certify the exact block identity and squared-Frobenius interference relation.
- `tests/test_suffix_leakage_transport.py` checks 1200 independent 2D rational projector/product examples, a 3D case, Jordan shears, rotation cancellation and dimensions.
- `MathCan/SuffixTransport.lean` formalizes the 2x2 *natural-number block multiplication skeleton* in Init. The analytic norm bounds and empirical 128D claims are **not Lean-formalized**.

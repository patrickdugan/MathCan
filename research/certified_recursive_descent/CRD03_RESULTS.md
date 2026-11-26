# CRD-03 result | Reachability supervision fails under depth shift
2026-11-26. Registered protocol: CRD03_PROTOCOL.md, commit 39bf47fe3165c85bf9fad5381fe4dc80c6898f19. Implementation frozen at f600743ff931647e4ef66acb289e6af70b1c66cd before execution. Receipt eea093efbab807f64a1503bce05c039e38cd6d06. Status: FAIL for learned scheduling hypothesis; PASS for bounded executable verification. No trained full TRM or BPD intervention.

## Method and results
All policies use identical exact arithmetic pre-verification and verified pending destination banks. This changes the interface from CRD-02; compare only within CRD-03. Same bank cap, same call ceiling; realized calls differ. The bank excludes the stored paths, observed-node maps and fixture from its count; these are shared overhead, not measurements of RAM.
Train on 512 fresh development roots, 2,048 trajectories (LIFO/random x cap 4/16), 32,732 labeled frontier entries, 19,996 positive. Binary cross-entropy with 64 batches of 32 sampled rows per epoch, 16 epochs, SGD step .08, deterministic seed. The linear model has 8 parameters; three-step tied recurrent tanh scorer has 137. Gradient finite-difference check max abs error 1.96e-11. Validation selects epoch 1 linear and epoch 16 recurrent from epochs 1/4/8/16; both solve 122/128 validation roots. No test-based checkpoint selection. Fresh test 256 deeper, wider roots; 9,216 test episodes and 537,346 verified calls, zero false accepts.

| Policy (cap 4) | 32 calls | 64 calls | 128 calls |
|---|---:|---:|---:|
| LIFO / depth | 16 | 196 | 215 |
| FIFO | 0 | 1 | 201 |
| Random | 1 | 107 | 223 |
| Linear | 0 | 2 | 203 |
| Recurrent | 0 | 2 | 207 |

At primary cap 4 / budget 64, recurrent vs depth: 0 wins, 194 losses, exact two-sided paired sign p=7.96546e-59 (descriptive for this generator, not a claim about all tasks). Recurrent vs linear: 0 wins and losses. At cap 16 / 128 calls, depth solves 254, linear 52, recurrent 44. See full receipt, including score evaluation counts and candidate peaks. In primary comparison, depth averages 45.20 charged calls and recurrent 63.96; both peak at four retained candidates. The JS execution took 10.621s including data generation, training and replay in the execution isolate; not an isolated CPU or RSS benchmark. Independent replay checks verified arithmetic, reachable expansion, no repeated edges, counts and successful path; capacity is checked using instrumented counts rather than replaying evictions. Node entrypoint still needs standalone invocation. Training and test code bodies did execute.

## Mechanism: static reachability is a bad utility label
Post-hoc diagnostic on DEVELOPMENT only, using the previously selected weights:
| Absolute steps remaining | Training labels positive | Mean recurrent score |
|---:|---:|---:|
| 0 | 0% | 31.55% |
| 1 | 55.94% | 42.23% |
| 2 | 61.18% | 56.87% |
| 3 | 70.24% | 69.51% |
| 4 | 75.32% | 75.48% |

Terminal goals are detected during verification, so retained terminal candidates are all non-goals. Earlier candidates have more paths that could reach the goal and get high static labels. The scorer ranks shallow candidates highly, delaying progress toward the hidden goal. The linear model's depth coefficient is negative and remaining-depth coefficient is positive. This is consistent with the catastrophic depth/budget shift, though this diagnostic does not isolate every causal factor. In a layered DAG with a hard call ceiling, classification of eventual feasibility is not the same objective as maximizing budgeted success. The original objective was intentionally a proxy and should now be rejected as a stand-alone scheduler target.

## CRD-04 proposed replacement (not executed)
Let s be the entire observed pending bank, R remaining verifier calls, and H a fixed fallback policy. For a legal action e, define Q_H(s,e,R)=E[1{H reaches a certified goal in the remaining budget} | do(expand e)]. For a retention decision the action is a subset, or a single eviction when one slot over capacity. On development roots only, clone the observed search state and run paired counterfactual continuation with identical fallback and budget. Use (Q(e)-Q(e')) as a pairwise advantage target; include a call penalty only after the primary success label is defined. Compare a progress-safe residual score D(e)+lambda*f_theta(s,e,R) with learned unrestricted policy, depth-only and random ties. Define D lexicographically or use a bounded residual that cannot invert different depths, then separately ablate this constraint. If all counterfactuals tie, retain them as ties, not fabricated preference labels. Restrict observation to the reached frontier; teacher-only hidden graph access never reaches the deployed policy. The original CRD-03 test seeds are retired from future model selection; choose new disjoint splits and register protocol before testing. Evaluate paired wins/losses at equal capacities and budgets; include memory bytes and training time if run locally. A higher proxy classification score is insufficient. This proposal is not yet a registered experiment.

Source limitation remains: the Cogentic main PDF and companion Lean formalization are unavailable through prior retrieval attempts. CRD-01's finite Lean candidate has not been compiled. This research is a synthetic scheduling experiment, with no new claim about factorization or ECDLP.

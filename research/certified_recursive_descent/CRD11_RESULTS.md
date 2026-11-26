# CRD-11 | Learning Bellman advantages for information acquisition
2026-11-27. CRD-11A protocol 78c632b256b7c56116555172fab65d4ae70b7709; source 9e4df981a837f3baf7da74aec10539657099a161; receipt 7f9561c7e7af42f2faf6d96029a241278090b146. CRD-11B follow-on protocol c01076a04adb7a09c77d6b3792417f2a5aa13256; source 9ba702706391907f747c9b33fac9eff3e2798a4d; receipt 978d93bc5a61e048a720b8102bb7118731512962. Positive full-feature transfer relative to cheap sensor/marginal controls, but no demonstrated advantage over local DP and a negative result against rollout. Removing local Bellman features fails on fresh roots. No full TRM/BPD, actual physical memory or factoring result.

## Finite adaptive task
Each independent branch has six latent states, three corresponding to possible successful terminal probes and three infeasible. Before probing, pay for 1–3 sequential noisy binary sensors. Their predicates/accuracies are public; posterior weights updated by integer Bayes and gcd normalization. Probes cost one, failure eliminates its candidate, success stops. Capacity counts active branches; opening a branch when full must irreversibly abandon one active branch, modeled as explicit distinct actions. Branches with zero feasible mass cease to occupy capacity. Each continuation strictly reduces remaining budget. Root seeds, latent state, and future observations excluded from learned inputs. Exact expected success calculated by finite memoized Bellman recursion. Sensor transitions and successful probes have exact semantic probabilities; this task has no external theorem-proving or arithmetic verifier calls. Thus do not report simulated "false accepts" or equate these expected action costs with actual CRD-10 certificate checks.

Training uses two branches with 1–2 sensors, cap1/2 and budgets3–5. Test ID retains the two-branch shape; OOD has three branches with up to three sensors, budgets4/6. Root splits are disjoint and checkpoint selection uses only 96 validation roots. All comparators share legal support and action costs; no-feedback controls still receive legal support exclusions. The teacher and strong rollout/optimal references can evaluate the known synthetic transition law but do not inspect hidden outcomes.

## CRD-11A frozen teacher and training
384 development roots; teacher 18,957 DP states, 93,835 outcome transitions and 47,060 action evaluations. Reservoir selected 7,538 states, including 6,596 with nontrivial action differences. 21,108 action labels Q*-V* including 10,322 zero-advantage optimal actions (not necessarily all distinct ties), 1,063 eviction labels/states. Teacher features include exact single-branch Q/V (and other-branch/evicted-branch V); these use public local beliefs and the remaining budget, not multi-branch teacher Q at inference. Teacher local feature computation adds 16,390 local DP states and 97,371 transitions. State-uniform then action-uniform SGD, 16 epochs, 64 batches x32 per epoch, lr .08, half-squared-error gradients (MSE objective up to constant). All heads select epoch16 using exact mean validation policy success, tie-break expected calls: linear .542377, MLP .535994, recurrent .546831. Param counts 21/177/136. Maximum gradient finite-difference error 9.57e-13. Recurrent scorer runs three tied tanh updates from zero per action; it is an action head, not a persistent recurrent memory model.

## Main OOD result
192 roots per configuration, primary cap2 budget6. Conditional success averaged across roots (not empirical binary trial success), exact model fixed. All policies evaluated with correct observation law, including the intentionally weaker controls.

| Policy | Success % | Mean expected calls |
|---|---:|---:|
| Optimal | 76.6444 | 4.9921 |
| One-step sensor-policy rollout | 74.6033 | 4.9144 |
| Local single-branch lookahead | 72.8739 | 4.5871 |
| Recurrent | 72.7384 | 4.2912 |
| Linear | 71.8650 | 4.2295 |
| MLP | 69.3496 | 4.0673 |
| Marginal/probe-first | 68.5315 | 4.2741 |
| Sensor-aware | 68.1886 | 4.0776 |
| Random eviction | 68.2089 | 4.0784 |
| No-feedback | 65.9259 | 4.3153 |
| Depth/probe-first | 60.1644 | 4.5434 |

Primary paired recurrent gain over sensor +4.5497 pp, root bootstrap 95% percentile interval [3.6013,5.5365] pp, wins/losses/ties 124/23/45. Over linear +.8734 pp [.5084,1.2620], over MLP +3.3888 pp [2.5985,4.2268]. Against local -.1355 pp [-.6385,.3142], against rollout -1.8649 pp [-2.5856,-1.1086], against optimal -3.9060 pp [-4.5064,-3.3415]. 2000 deterministic bootstrap resamples; descriptive, no multiplicity correction, no significance claim beyond the reported intervals. Recurrent expected regret is 3.906 pp. The local baseline remains strong and recurrent has no identified superiority over it. Full feature head may use fewer expected environment actions while requiring substantial local inference work. It is not an isolated speed comparison.

Secondary ID cap2 budget5: recurrent .639139, local .635208, rollout .665850, sensor .607054, optimal .669095. OOD cap1 budget6: recurrent .702396, local .711743, rollout .733828, sensor .670619, optimal .763221. In primary cap2/6, recurrent expected evictions .00307 per root, optimal .04911, local .01808; at cap1/6 recurrent .09102, optimal .26114. Eviction labels exist but rare active policy eviction at cap2; these results do not isolate or establish learned eviction gains. The random-eviction control changes only victim choice once sensor-aware expansion chosen; it is not cap-matched random action selection.

Costs across both OOD cap2 budgets (shared memoization): recurrent 17,422 scored actions and feature evaluations, 30,528 local DP states, 129,855 local transitions; local baseline 17,888 scores, 27,371 local states, 126,192 local transitions; rollout 150,270 total action scores including its continuation policy, 41,056 rollout states, 78,212 rollout continuation transitions and 42,115 extra lookahead transitions. Exact global oracle 151,956 states and 929,749 outcome transitions. Policy evaluation recursion costs are distinct from policy scoring work. Full head does not demonstrate a computation saving over local DP: both use it, head adds neural work. Peak 12 active-belief numeric slots under cap2 (96 bytes if float64), ignoring public priors, weights, interned state caches, DP memoization, JS objects, audit and all scratch. This is an active-state payload convention, not a bounded allocator. End-to-end JS isolate 29.307s not controlled performance timing.

## CRD-11B preregistered ablation on fresh OOD roots
Retrain each head on same deterministic labels and validation roots with four local-DP features (indices 9,10,12,18) zeroed. Cheap feature implementation bypasses local Q/V computations completely; integer posterior conditioning and one-sensor expected best remain. Freeze new checkpoints before evaluation. Full heads reuse original frozen weights. Fresh seeds 1780001..1780192, cap2, budgets4/6. All 576 cheap-head root evaluations pass zero local DP state/transition/query checks; validation also enforces zero. Teacher still computes exact global/local values offline. No test tuning. All cheap heads select epoch16.

| Policy | Budget4 success % | Budget6 success % |
|---|---:|---:|
| Optimal | 59.0510 | 75.6138 |
| Rollout | 57.4516 | 73.8341 |
| Local lookahead | 57.1107 | 72.0757 |
| Full recurrent | 56.5233 | 72.2676 |
| Full linear | 55.4860 | 71.7045 |
| Full MLP | 54.3135 | 69.0709 |
| Sensor-aware | 54.0633 | 68.0473 |
| Cheap linear | 48.6524 | 59.2702 |
| Cheap recurrent | 45.9016 | 58.2622 |
| Cheap MLP | 45.5678 | 57.6744 |

Primary cheap recurrent vs full recurrent -14.0054 pp, bootstrap [-15.8622,-12.1406], wins/losses/ties 4/160/28. Vs sensor -9.7852 pp [-11.5591,-8.1333], 12/138/42. Vs cheap linear -1.0080 pp [-2.2129,.1264], vs cheap MLP +.5878 pp [-.3741,1.5529]. All cheap heads perform below sensor and marginal at both budgets. No evidence of cheap amortization success. Local-DP feature block carries essential predictive information for these trained heads. This is a matched removal-and-retraining intervention, not an isolated change of architecture or proof that no cheap model can solve the task.

Cheap recurrent scoring across both budgets: 11,816 features/scores and zero local DP states/transitions; full recurrent 17,540 features/scores, 29,669 local states and 126,914 local transitions. Reduced work proxy accompanies a large utility loss. Mean expected calls at budget6: cheap recurrent 4.0743, full 4.2920, sensor 4.0586. No cheap-head eviction observed in expected evaluation at cap2, so cannot claim eviction competence. End-to-end JS isolate 16.253s.

## Mathematical link to advantage error
For finite action-cost-one decision problems with terminal reward 1 on success and 0 otherwise, let V*(s,b) be optimal remaining expected success. Let A*(s,a,b)=Q*(s,a,b)-V*(s,b)<=0. For any policy pi, the difference V*(s0,B)-V^pi(s0,B) equals E_pi[sum_t -A*(S_t,A_t,B-t)] over actually reached nonterminal decision states. Proof: write Q* as immediate success reward plus continuation V* on nonterminal successor; sum conditional Bellman residuals along the trajectory. Intermediate V* terms telescope, terminal continuation zero. If estimated advantages satisfy uniform |Ahat-A*|<=epsilon_t over every legal action at reached states, choosing maximal Ahat implies true regret per decision <=2 epsilon_t; compare to any optimal action of true advantage zero. Therefore total regret <=2 E_pi[sum_t epsilon_t], and if all errors <=epsilon, <=2B epsilon (also at most 1). A true action margin exceeding 2epsilon certifies the optimal choice. This requires reached-state uniform error, not only training MSE or average posterior error. No such error bound was established for the fitted heads. It complements CRD-10 interval-certified exact ranking and can guide a future residual scheduler.

## Verification and next work
11A: 16,896 policy/root/budget expectations, 768 budget monotonicity checks, four hand identities, 24 independent latent-world policy replays over 2,304 worlds, max error 1.23e-15. 11B: 4,224 policy/root/budget expectations, 12 independent replays over 2,592 worlds, max error 3.34e-16. All capacity and probability-mass checks passed. These are 21,120 exact-model evaluations, not 21,120 physical episodes. Evaluation and audits use floating arithmetic on rational-weight posterior states; "exact" means exact finite transition recursion rather than sampled Monte Carlo, not formal rational proof throughout. Independent replay reuses the frozen decision policy but enumerates latent worlds/sensor observations separately. Actual RAM profiling, standalone Node execution, Lean compilation and Cogentic original paper audit remain outstanding. Reproduction: node research/certified_recursive_descent/information_gain.mjs; node research/certified_recursive_descent/information_gain_ablation.mjs.

CRD-12 proposal (unregistered): distill the local Bellman table directly instead of removing its four values and asking the advantage head to relearn both local dynamics and global allocation from one scalar label. Exploit branch independence: local state (normalized belief, remaining sensor predicates/accuracies, budget) maps to exact local action Q and V; train a compact reusable local predictor with supervised local-Q/V targets across depths and budgets, and use its predictions in the frozen/retuned global head. Compare against cheap analytical local formulas, memoized exact DP, fitted local surrogate plus heuristic global policy, full exact-feature head, and global rollout. Test actual error distributions, action-margin certification with fallback to exact local DP, resulting utility and amount of exact inference avoided. Freeze new splits; include eviction stress where several simultaneously promising branches compete and a full-tree correlated extension separately. No new crypto/number-theory claim follows from this sequence of synthetic experiments.

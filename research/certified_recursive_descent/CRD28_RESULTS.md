# CRD-28 | Boundary and demand-pruned allocation
2026-11-27. Prospective protocol f83651245026f5e1fa241eeea1a22b08ccae6aa2; source 5a8495561e0b1dc230f624386e11c42e32256d8e (blob d5cc88f24c79276d0315828b97aa8bff98a72ddc), CRD-27 interface-only export 9d0e8c19bebc13805594a2905ff1c92ace223ac3. Receipts standard 571f8b62d176379a353f2b3caf6f2ff962ccfeee (803b170134e7a627f74d5494ff500988daaed891), five 0ae86ab4ba6a745bf162a59a29c18197d8c35797 (f609a302ee31f04be81e9568a7c831243cf35b12), seven b50a095dab8dc58ddbbf0d974d3e4c591a0ac5dd (1ad3d44604a8f2e1ea316113fc73c4996010ff8b). All read back. No fitting or post-outcome changes.

## Mathematics
Use CRD-27's exact static at-most-budget min-product fold, with joint local likelihoods and omitted neutral factors. For options O_i containing zero and increasing positive values, D_0(r)=1, D_i(r)=min_(t,v in O_i,t<=r)(1-v)D_(i-1)(r-t). Since D_0 is constant, the first factor equals one minus its best affordable local value, maintained by a monotone option cursor. Boundary computes this directly and only r=b for the last factor. No other first-factor convolution candidate can improve the cursor result. Last is the frozen terminal-only fold. Ordered sorts by increasing retained option count, stable canonical ties, then uses Boundary; commutativity justifies reordering the independent static factors.

Demand sets R_n={b} and R_(i-1)=union_(t in O_i){r-t:r in R_i,r>=t}. The zero-cost option is included. Forward evaluation only on R_i has all dependencies by construction, hence equals full fold on demanded indices by induction. Use one unsigned bitmask per factor, shifting right by t, for B<=30. Demand uses Boundary with these masks; DemandOrdered additionally sorts. Each bitset shift, mask slot, forward scan (including skipped budgets), first cursor scan/advance, sorting comparison and convolution candidate charged. This is an exact real-arithmetic transformation for the retained options, subject to inherited support tolerance and double precision. Unit audit 2072 comparisons to exhaustive BigInt rational numerator and full terminal fold, 1577 skipped cells, max error 1.11e-16. Identical deterministic unit test repeated per cohort. No physical speed claim.

## Frozen traces
20 standard roots 3420001..3420020 (3 branches, B6, up to3 sensors),16 five 3430001..3430016 (B6, up to2),12 seven 3440001..3440012 (B5, up to2), cap2 throughout. Fixed CRD-25 grouped initial/first/second and actual eviction trace; 9723 queries,5475 distinct within roots,5195 one-factor and4096 two-factor changes,432 initial/repeated parents. Exact dense comparison on each query; all budgets separately checked first two roots/cohort.

| Kernel | 3 work | 5 work | 7 work | Pooled work | Pooled candidates |
|---|---:|---:|---:|---:|---:|
| Direct | 46111 | 144731 | 186631 | 377473 | 212840 |
| Scalar | 53358 | 169619 | 217147 | 440124 | 212840 |
| Last | 45354 | 155501 | 197642 | 398497 | 175163 |
| Boundary | 42665 | 149236 | 193401 | 385302 | 128609 |
| Demand | 49348 | 182753 | 252211 | 484312 | 92573 |
| Ordered | 44385 | 159615 | 217998 | 421998 | 131320 |
| DemandOrdered | 52095 | 200090 | 288590 | 540775 | 111716 |

Boundary saves 3.31% vs Last and 12.46% vs bounded Scalar pooled, lower work on every root. Five primary Boundary vs Last mean -391.5625 units/root, paired 95% descriptive interval [-417.875,-368.125],16 lower. Demand vs Boundary +2094.8125 [2029.75,2166.3125],16 higher. Boundary saves 39.58% of Direct convolution candidates but pooled work remains 2.07% higher than unbounded Direct. Demand cuts candidates further but 37273 shifts, 24106 skipped forward cells and scans offset saving. Ordering costs 37320 comparisons pooled and raises work. All joint modes 6852 likelihood products vs Scalar13662. Report fixed workload proxy, not elapsed-time advantage.

## Policy
Same 2k/8k total charged work, decision quota min(R,ceil(2R/b)), frozen graph, setup, fallback. All new kernels have same fixed scalar numeric payload 3584/3072 bytes, metadata/temporary bitsets, DP, graph and evaluation excluded. No total memory or hardware FLOP claim. Exact finite expected success, not observed binary trial rates.

| Cohort/ceiling | IncCheap | Metered2 | Scalar | Last | Boundary | Demand | Ordered | DemandOrdered | Boundary2 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3/2k | .709622 | .718096 | .710907 | .709622 | .709622 | .711845 | .709622 | .711845 | .724913 |
| 3/8k | .761155 | .767215 | .755473 | .761155 | .761155 | .760802 | .761155 | .760599 | .767215 |
| 5/2k | .734735 | .732420 | .734735 | .734735 | .734735 | .734735 | .734735 | .734735 | .732698 |
| 5/8k | .788127 | .750826 | .786356 | .791730 | .791730 | .786407 | .787236 | .784266 | .750840 |
| 7/2k | .661213 | .659449 | .661213 | .661213 | .661213 | .661213 | .661213 | .661213 | .659449 |
| 7/8k | .747020 | .680645 | .743951 | .754737 | .754737 | .723222 | .753320 | .723222 | .706448 |

Exact/receding2 unrestricted 3=.769496/.767215,5=.823138/.818434,7=.784368/.783861. Seven horizon shorter, no controlled scaling curve. Primary five8k Boundary ties Last on all16; Demand vs Boundary -.005323 [-.013203,-.000466],0/4/12. Boundary vs Scalar +.005374 [.000308,.013597],5/0/11; vs IncCheap +.003602 [0,.010045],3/0/13. Seven8k Demand vs Boundary -.031515 [-.057021,-.008573]; Boundary2 vs Metered2 +.025803 [.004625,.052191],4/0/8, secondary. Standard Boundary2 matches Metered2 at 8k with 3561.16 vs3751.21 work; five Boundary 7032.37 vs Last7034.40, Scalar7098.34; seven Boundary7251.43 vs Last7220.75, same utility. All paired intervals 2000 fixed resamples, descriptive and unadjusted. Work expectation is path-dependent; fixed trace comparisons isolate arithmetic. Freeze Boundary/Last for later comparison; demand pruning not recommended at these tiny horizons.

## Verification
48 roots,864 metered policy evaluations+96 unrestricted=960;139297 oracle states,23563 decision visits,92054 complete Q checks,11514 numerical certificates. 68061 trace value and38717 all-budget comparisons; max1.11e-16. Every chosen regret, gap/telescoping, resource and environment ceiling passed, max interval violation2.22e-16, gap violation zero, scalar peak132. All receipts read back. Source-body JS execution, no standalone Node/Lean, hardware RSS/time, real verifier or original Cogentic proof audit. No number-theoretic result. Reproduce node research/certified_recursive_descent/demand_pruned_allocation.mjs [--population|--larger].

## BPD/LLM transfer
The strongest general lesson is eliminate known redundant algebra first and meter the cost of deciding what to prune. BPD TiedComponentLinear currently forms dense residual W-(VU)^T per invocation. Let A=XV,Y=XW^T, component mask m, residual mask d (1 when absent). With calibrated means mu_c and mu_d (zero for zero-ablation), write before bias/norm is dY+[(m-d)A+(1-m)mu_c]U+(1-d)mu_d. This removes dense VU and fuses two writes. Keep exact existing sphere rescale, bias and routing semantics. Target-mode ablations already use selected components. Training masks need their gradients; do not skip zero-weight components with trainable masks. Cross-layer/dynamic activation pruning needs separate error/verification contracts; dense attention creates dependencies across tokens, nonlinear residual paths can propagate changes. Terminal-only LM-head logits at the last requested token and shared-prefix/KV reuse under identical causal histories are exact structural analogues; masked vocabulary softmax generally changes distribution. BPD transfer is a separate kernel test, not evidence of LLM tokens/s from this synthetic gym.

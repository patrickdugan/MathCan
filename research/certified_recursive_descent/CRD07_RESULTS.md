# CRD-07 | Noncommutative compositional memory
Protocol 57896a6deae808737d72401ddbdf02054a8c3579, implementation de89ef21cb86c42b62d0ab6de7e1b5b71d9f170d, frozen receipt 2ed24344bc5c857ac361091ef27c49fb31943a5c. Post-hoc conditional regret receipt 2917ceb369c10f4709f5070199d17e7f923e846e, reproduction source 3fd9b8c4ca2b3c7d3b53939003b9a508b8a31d1d. Status: learned structured channel transfers to long histories; generic recurrence fails; superiority to hard ordered product is unestablished by the primary paired test.

## Mathematical audit
S3 represented as (k,s), k modulo 3, s modulo 2, product (k+(-1)^s*l,s xor t). Its real representations are the trivial and sign characters and rho(k,s)=R(2*pi*k/3)diag(1,(-1)^s). For normalized p, omit trivial coefficient and retain sign expectation a and 2x2 matrix M=E rho(g). Independent right increments give a'=a*a_increment and M'=M*M_increment, in order. Inversion p(g)=(1+sign(g)*a+2 Tr(rho(g)^T M))/6. Direct normalized posterior can also be encoded in five real coordinates; the advantage of Fourier coordinates is blockwise arithmetic, not information-theoretic storage compression. Precomputed channel blocks require nine multiplication and four addition operations per update, versus 36 products for naive direct convolution, excluding lookup/readout and runtime overhead. No measured speed claim.

All 216 associativity checks, 36 representation products, six inverses/basis inversions and 36 missing-increment bijections passed. 18 of 36 ordered group pairs do not commute. Exact rational enumeration: 258 observed histories, 47,988 latent paths. All direct and Fourier posteriors matched the rational results within tolerance. On 8,192 further true/shuffled histories across both test regimes, max exact direct-vs-Fourier coordinate error 1.513e-15, max learned direct-vs-Fourier error 1.791e-15. Gradients checked by central finite differences, max error 3.749e-11. Proper subsets of observations leave the hidden product uniform under the independent uniform increment law: one omitted independent uniform increment is mapped bijectively to every group element by multiplication on either side by fixed products.

## Frozen training and sequence test
8192 training sequences length 2–7, 1024 validation length 8–10, 2048 paired test sequences per regime length 11–16. Training level c in {0,.5}; shifted test c in {.75,1}. Same uniforms, changed latent draws. Learn two categorical noise kernels using terminal CE only, affine mixture known, identity-favoring initialization; group structure and exact filter architecture are supplied. Selected epochs: learned 12, RNN 1, window/full MLP 8. Channel endpoint L1 errors .01875164 and .06327067. The second endpoint is extrapolated from training mixtures. Learned weights and kernels in receipt.

| Model | Parameters | Persistent scalars | Original correct /2048 | Shifted correct /2048 |
|---|---:|---:|---:|---:|
| Exact Fourier | 0 learned | 5 | 1166 | 605 |
| Learned Fourier | 12 | 5 | 1166 | 605 |
| Hard group product | 0 | 1 | 1166 | 605 |
| Generic RNN | 101 | 5 | 325 | 350 |
| Window MLP | 111 | 14 | 317 | 333 |
| Full-history MLP | 244 | 112 | 302 | 331 |
| Uniform | 0 | 0 | 325 | 350 |

Learned CE 1.370652 / 1.742300, exact 1.368518 / 1.736700. Sum-of-class posterior squared error .000688683 / .003113590. Hard product has the same realized MAP correctness, but is uncalibrated (one-hot output). The two-step window is information-limited by construction; full-history model's padded early coordinates are unseen during short-length training. No generic architecture impossibility result. Order permutation of the same observed pairs changes hard composition on 1371/2048 sequences in both regimes. True learned accuracy 1166/2048 falls to 499/2048 after permutation; shifted 605 falls to 375. Exact posterior mean L1 change .675839 / .258850. Permuted observations are an intervention, not another correctly specified posterior for the original ordering.

## Streaming retention test
Each regime 192 fresh roots of 16 independent histories; all prefix transitions deliberately valid, every symbol gated by the exact CRD-01 rational verifier, and one/four terminal probes checked against ordered latent product. All histories must be streamed before probing; this is top-k selection, not adaptive proof search. Identical graph/certificates for paired true and shuffled views. Feasible roots 184/192 original, 188/192 shifted.

| Policy | Original one probe | Original four probes | Shift one probe | Shift four probes |
|---|---:|---:|---:|---:|
| Exact Fourier/direct | 105 | 159 | 50 | 128 |
| Learned Fourier | 104 | 157 | 50 | 124 |
| Hard composition | 97 | 156 | 54 | 121 |
| Generic RNN | 28 | 98 | 43 | 111 |
| Window MLP | 30 | 103 | 28 | 107 |
| Full-history MLP | 28 | 95 | 22 | 100 |
| Random ranking | 31 | 104 | 31 | 110 |

Primary learned vs hard: 21 paired wins, 14 losses, p=.3105; vs exact 1/2 p=1; vs RNN 85/9 p=1.20e-16. Learned true vs order-shuffled 104 vs 43, 70/9 p=7.78e-13. Shifted learned 50 vs hard 54, 14/18 p=.597; vs shuffled 33, 39/22 p=.0396. Descriptive unadjusted paired tests. No observed superiority to hard composition. Shift weakens the signal and exposes channel estimation error. Generic RNN has chance-like sequence results; its shifted one-probe search result is not significantly different from learned Fourier at this sample size.

Executed prefix checks: 1,495,296 across both regimes; 27,107 terminal probes; 13,824 logical policy/root/probe episodes. Each one/four-probe configuration reuses the same prefix stream, so logical prefix checks 2,990,592. Zero false accepts. Primary mean 217.3333 calls including terminal; logical float64 active plus cap4 numeric payload Fourier/RNN 200 bytes, direct 240, hard 40, window 560, full 4480. Excludes cached scores/IDs/parameters/lookups/fixture/object overhead. Exact direct and Fourier scheduler probe traces agree after score quantization at 1e-12. End-to-end JS isolate time 16.987s, no standalone Node invocation or measured process RSS.

## Post-hoc conditional utility and certified error bound
Using frozen test histories, compute conditional V(S)=1-product_(i in S)(1-p_i), with p_i the exact target posterior. Independence of branches conditional on their observations and target makes this an exact expectation under the synthetic law. This evaluates policy selection without terminal Bernoulli noise; it is a post-hoc diagnostic, not a newly registered endpoint or real search guarantee.

| One probe conditional success | Original | Shifted |
|---|---:|---:|
| Exact Fourier | 56.2586% | 29.7038% |
| Learned Fourier | 56.2118% | 29.6178% |
| Hard product | 53.1382% | 29.0640% |
| RNN | 16.0054% | 16.6743% |
| Uniform ranking | 17.8663% | 16.9535% |

Learned expected one-probe regret against exact = .000467907 / .000860125 (0.0468/0.0860 percentage points). Four-probe regret .002110222 / .008554066. Exact expected four-probe success .835919882 / .669465753, learned .833809660 / .660911687. This diagnostic does not require comparing sampled binary outcomes or claiming statistical significance on a population beyond these frozen histories.

General block error theorem. For each nontrivial unitary irrep rho of a finite group G, let A_t,B_t be exact and approximate increment Fourier matrices, delta_t=||A_t-B_t||_op, r_t=max(||A_t||_op,||B_t||_op). Ordered product telescoping and submultiplicativity yield ||A_1...A_L-B_1...B_L||_op <= sum_t delta_t product_(j != t) r_j = D_rho. Inversion and |Tr(U^*E)| <= d_rho||E||_op give ||p-q||_infty <= |G|^(-1) sum_(rho nontrivial) d_rho^2 D_rho. For S3 this is (D_sign+4D_standard)/6. For uniform delta,r, bound D <= L delta r^(L-1). For any noise kernel K with minimum mass m, write K=|G|m*Uniform+(1-|G|m)*K_residual; the nontrivial uniform Fourier blocks vanish and residual norm <=1 by convexity of unitaries. Hence r <=1-|G|m when applied to both channels with their shared lower mass. Multiplication by the observed group matrix preserves operator norm. These estimates concern absolute posterior error, not relative error when the signal decays. Together with CRD-06 top-k regret bound 2k epsilon, they certify conditional loss under independent branches (add score quantization tolerance for rounded ranking). The numerical diagnostic uses floating operator norms and tolerance 1e-12, not interval arithmetic or a Lean proof.

All 6144 branch error checks and 768 root/probe regret checks passed with tolerance. Max branch coordinate error .0744266 original / .0561925 shifted, mean branch bound .0915959 / .1158642. Mean target-specific root epsilon .0241682 / .0464124. Bounds are conservative; observed mean decision regret is much smaller. Diagnostic replays all included observed solve counts from frozen receipt. Source-body execution checked; new Node import guard and diagnostic CLI have not been invoked as standalone processes.

## CRD-08 proposed, unexecuted
Move from supplied group blocks to learned operator identification with noncommuting transformations and a held-out relation alphabet. First audit identifiability up to conjugation/gauge: state change M -> S M S^-1 and corresponding readout preserve predictions, so compare invariant products/eigenvalues or aligned blocks rather than raw coordinates. Train one shared transition model across multiple terminal targets and sequence lengths; include known group/product oracle, direct learned stochastic convolution, true block oracle, learned unconstrained matrices and parameter-matched generic RNN. Test whether learned block structure transfers under held-out transition compositions and observation-channel shifts. Add a genuine budgeted branching search where new observations can alter pruning, and a coupled-branch control to test limits of independent top-k utility. No new factorization/cryptography result. Original Cogentic PDF and Lean formalization remain unaudited; CRD-01 Lean ledger uncompiled.

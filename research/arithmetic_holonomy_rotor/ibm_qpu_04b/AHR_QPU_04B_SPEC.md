# AHR-QPU-04B: history-dependent memory lifetime and refocusing

Parent hardware commit: `a9e204ca0c214578751f75d8c91a20a84823f652`, draft PR #271. IBM Kingston job `dc2b0g5s2omc738bn0d0`, 155,648 shots (76 × 2,048), 45 free QPU seconds. Last recorded allocation 416 s is historical. No new cloud access or execution is authorized by this study.

## 1. Raw evidence and confounding

Using the immutable parent count ledger and ordered circuit manifest, independently recompute the joint correct-and-return event, spatial return, and internal conditional Y. At 24 µs AB returns on 1,639/2,048 shots, but only 146 of the returns have the requested negative Y. BA returns on 1,629 shots and 1,572 are correct. The primary failure is loss/reversal of the specified internal order readout, not spatial leakage induced by dwell.

Equal-prior conditional binary-distribution TV is 0.05409 at 24 µs; the plug-in optimal accuracy is 52.704%. With nonreturn as an erasure, the plug-in TV is 0.04346 (52.173%). Full 16-outcome histogram plug-in accuracy is 53.931%. The latter is optimistic if trained and tested on the same counts, and differing spatial readout maps may leak a classical implementation label. Use the fixed sign decoder with randomized erasures as the operational endpoint; do not claim measured quantum trace distance from any one readout basis.

Routed circuits use 104 CZ gates, depth 318 without dwell, 12.616 µs nominal duration, initial internal physical site 3, and final internal site 16. AB spatial measurement map is [1,2,3], BA is [3,1,2]. Both direct references use physical site 3. A reference on the same dwell site is needed. The included QPY audit checks the exact archived file digest, ordered case IDs and the first four protected edge operations. It evolves both basis states of the initial internal mode through the compact native prefix, compares the two resulting columns with W_A or W_B up to a scalar phase, and determines the mid-loop physical site by the support and unitary test. Until this passes, the dwell site is unverified. Do not infer the site from the final measurement map.

## 2. Channel model and descriptive numerical fit

At the orthogonal fixture, A first sends the internal Bloch vector from +Z to +Y, B first leaves +Z. The AB final unitary flips X,Y; the BA final unitary maps Z to Y and Y to -Z.

Under a common Z rotation by phi=omega*t and transverse attenuation kappa, the final ideal-position internal Bloch vectors are

    r_AB = (kappa sin phi, -kappa cos phi, 0),
    r_BA = (0, 1, 0).

Thus D=(1/2)sqrt(1+kappa²+2 kappa cos phi), while Y-only distinguishability is (1+kappa cos phi)/2. This is a conditional toy model with ideal spatial return. When kappa=1 and phi=pi the two encoded states collide. A stationary sign-preserving dephasing model alone cannot explain a large AB sign inversion; affine biases, nonstationary errors, and route-dependent channels remain alternatives.

Use only AB's four conditional binomial readouts for a descriptive profile fit. Grid frequency 0.04..100 kHz at 0.04 kHz spacing, use the final physical readout site's archived T2 as a fixed *reference* attenuation (not a measured mid-loop T2); obtain bounded sine/cosine coefficients by weighted linear regression and radial clipping; rank grid candidates by conditional binomial deviance. This is not an exact MLE or preregistered hypothesis test. Compare sign-preserving exponential decay and biased monotone exponential using a bounded approximate profile grid.

The independent receipt calculation finds routed 18.04 kHz (deviance 2.48), direct 8.96 kHz (1.63), order register 10.04 kHz (0.59). Routed sign-preserving decay has deviance ~1386.79 and biased monotone profile ~16.16. The routed oscillatory fit predicts Y=+0.760 at 16 µs and -0.465 at 40 µs; the biased profile predicts a high positive value at 40 µs. Four dwell samples cannot identify the channel or resolve all frequency aliases. Hold out 16 and 40 µs prospectively. Fix the old fit before collecting them.

## 3. Refocusing and balanced intermediate encoding

For ideal deterministic Z detuning during a dwell, the operation

    X Rz(phi/2) X Rz(phi/2) = I

restores the intended logical frame up to phase. Insert one X at the midpoint and the other at the end, on the certified mid-loop internal physical site. The pulse-count-matched sham places both X pulses adjacent at the end. Ordinary memoryless dephasing still removes transverse contrast; echo can refocus slow correlated phase errors but adds gate noise.

A separate mathematical extension chooses a common frame K for storage and K† for restoration, rotating the physical Z noise axis into n=(Y+Z)/sqrt(2) in the logical frame. For a pure dephasing channel E(r)=kappa r+(1-kappa)n(n·r), the final Y correct probabilities for both histories become (3+kappa)/4. This maximizes the smaller Y score over fixed storage axes: the two terms involve n_y² and n_z², whose sum is at most 1, so their minimum is at most 1/2 and equality is attained at the bisector. For the bisector the two final vectors are antipodal and D=sqrt((1+kappa²)/2); the usual Z-storage design gives D=(1+kappa)/2 when phi=0. This balances vulnerability in the toy model, and does not protect against arbitrary errors. Test numerically first; do not include unverified storage rotations in the initial physical pilot.

## 4. Next candidate experiment: simulator and synthesis first

The case generator freezes 120 fixed 1,024-shot settings and reserves up to 24 extra 512-shot eigenstate preparations across the actual internal physical sites (six +/- X/Y/Z calibrations per site). This is at most 135,168 shots. For each arm and label, measure X/Y/Z at dwell 0,8,16,24,40 µs; echo at 8 and 24 µs in X/Y/Z, and pulse-matched sham in Y. Include the mid-loop routed prefix at 0 and 24 µs in all bases and the 16 computational preparation/readout settings.

- **Routed full:** preserve the eight compiled native edge blocks from the archived QPY. Replace only the registered delay, insert physical echo/sham pulses on the audited dwell site, and change the terminal measurement basis without rerouting the protected link blocks. Validate exact full-space semantics, route boundaries, measurement permutations and mid-loop product state. Match padding and delay exposure where possible. For X/Y/Z, use separate native basis rotations, never infer X or Z from old Y counts.
- **Direct dwell-site reference:** perform W_A/W_B and the same interventions directly on the audited physical dwell site. If final readout site differs, calibrate both sites, report the limitation and use a separate terminal-site reference if the budget permits. Direct-gate comparisons remain different circuit families. A future compiler-locked transport control must match the gate schedule before making a causal routing claim.
- **Mid-loop:** after the first protected loop and optional dwell, read out spatial position and internal X/Y/Z, before the second loop. This separates storage failure from second-loop conversion.
- **Analysis:** all shots in joint return/correct denominator; compute conditional Bloch estimates and return separately; use independent basis shot counts and simultaneous intervals, physical Bloch-ball constraint for point estimate, retain raw counts and calibration/systematic sensitivity. Fit the archived frequency model only to old data; use fresh 16 and 40 µs as prediction checks. Estimate joint and worst-label gains of echo vs ordinary and echo vs sham, with a prespecified familywise interval. Record actual timestamps/spans and calibration changes when available. Stop on layout mismatch or failed controls.
- **Prospective gate:** no hardware GO until the exact prefix audit passes, compilation and ideal simulations pass, live calibration and physical placement are verified, and the expected interval and pulse-error stress indicate a useful discrimination. For hardware results, require the lower simultaneous bound of the echo improvement over pulse sham at 24 µs for routed AB to exceed 0.10, preserve BA within a prespecified 0.05 noninferiority margin, and report spatial return and X/Y/Z discrimination. These are design goals, not predicted outcomes. A failed criterion remains a result.

The candidate ledger estimates a provisional engineering cap with the historical 250 µs repetition delay, 12.616 µs route duration, 40 µs maximum dwell, 2 µs slack and the parent overhead rule. It is intentionally uncompiled and unapproved. A fresh physical manifest, duration/error estimates, present Open Plan allocation, and separate explicit job authorization are mandatory. No paid fallback.

## 5. Complexity boundary

This study explores stability of finite-dimensional order memory and coherent control. A single internal qubit remains efficiently classically simulable. Echo or a better storage frame does not imply computational advantage or establish any of Impagliazzo's five worlds. Link to COMP-02 through precision-resolved non-Gaussian witnesses only after matching resources and classical controls.

# AHR-QPU-04 routed order memory

The [pinned design](../ibm_qpu_03b/AHR_QPU_04_SPEC.md) encodes the cube position on q0–q2 and a two-level internal mode on q3. The two routes are 0→1→3→2→0 and 0→1→5→4→0. At the orthogonal fixture, the exact internal Y expectations are −1 for AB and +1 for BA. The routed circuits preserve all eight links and the shared position state. See the [simulation](RESULTS.md), [exploratory hardware pilot](HARDWARE_RESULTS.md), and [approved manifest](receipts/manifest.json).

## Reproduction

Use Python 3.12. These commands work offline with the saved calibration once the dependencies are installed.

```sh
python -m pip install -r requirements.txt
python -m pytest -q
python run_study.py --calibration receipts/calibration.json --out reproduced
```

Omit the calibration argument for an offline FakeFez baseline or add `--quick` for a smaller smoke study. The optional `calibration.py` command uses read-only IBM metadata when explicitly supplied an approved existing credential file. It selects a unique free Open Plan instance. The archived hardware launcher requires an explicit action and verifies the exact manifest digest. [Hardware replay instructions](HARDWARE_RESULTS.md#offline-replay)

## Measurement and controls

- The primary score is the probability of returning to position 0 **and** reading the correct Y sign. All shots stay in the denominator. Report return probability and conditional Y and accuracy separately.
- Compare the exact controlled edge block, separate controlled rotations and swaps, and a multiplexed rotation plus controlled swap. Select from two connected calibrated subsets and three initial permutations using the weaker orthogonal label on nominal Aer only. Use seed 381704 for native compilation. The full-space and intermediate-route checks are independent of that selection.
- Randomize the balanced label and control order with seed 228341. Use 2,048 shots for every setting in the synthetic count ledger and proposed manifest. Audit eight protected edge boundaries, native count and timing, readout maps, loss of explicit identity gates, and delay padding. Both link orders, commuting, identity, reverse, inverse, same-link, and pure-gauge controls remain in the workload.
- Compare a direct internal-gate reference and a baseline that writes a known order bit. These references use the same readout basis. The latter starts with the known label and measures how faithfully the register retains it. A 16-state preparation/readout calibration is sampled through a separate random stream.
- Assess memory at 0, 2, 8 and 24 µs and six held-out angle pairs generated from a fixed separate seed. Compare each held-out scan to direct gates. The fixed Y readout is tuned to the orthogonal fixture and can be suboptimal at other angles.
- The calibrated model includes native gate channels and single-qubit readout matrices. The frozen snapshot supplied symmetric assignment probabilities. The hardware report separately tests the asymmetric values returned for job start. Explicit idle blocks use calibrated relaxation. Terminal delays pad short controls to the target time where possible. Longer controls retain their native duration. Gate counts and channel placement can differ after duration matching.
- The simulation gate requires the primary mean and simultaneous 95% counting lower bound to reach 0.80, the calibrated Y signs to match, and the commuting contrast interval to include zero. Use Wilson intervals with a Bonferroni allowance across the two labels, plus a separately specified one percentage point systematic allowance per probability. The same checks apply under four predeclared noise scenarios. The coherent shift and additional gate and readout error assumptions are simulation stresses.

The exact manifest binds the QPY SHA-256, ordered cases, replayable calibration, physical mapping and an independent resource estimate that uses native durations and the backend repetition delay. The user separately authorized one exploratory run of that workload. Further jobs require a fresh manifest and separate approval.

The reported observables describe finite four-qubit circuit operation and two-level memory readout.

# AHR-QPU-04B native candidate implementation

The first [QPY audit](https://github.com/patrickdugan/MathCan/actions/runs/45278432839) passed all eight routes. Both labels move the internal mode from q3 initially to q16 during dwell and at final measurement. The maximum prefix operator error is 2.63e-15.

`compile_candidate.py` generates an **offline historical-snapshot** 132-circuit candidate: 120 × 1,024 plus 12 × 512 shots, 129,024 total. The 12 supplementary eigenstate calibrations cover +/- X/Y/Z on actual audited sites q3 and q16. It copies original native edge instructions from the QPY, compares each copied gate and wire, and inserts controlled dwell/echo/sham and basis readout operations at verified barriers. The candidate preserves 104 CZ gates in full routed cases, uses the certified q16 direct reference, and retains separate mid-loop measurements.

The direct reference matches routed time windows by padding before the first direct gate and after the second; exposure to particular states within these windows differs. Echo and sham have exactly two X pulses and the same nominal free idle duration; compare those two to control pulse count and elapsed time. Do not reroute or optimize across protected boundaries. The compiler intentionally does not connect to IBM.

Frozen historical Aer is evaluated on all cases. Extra simulator-only Rz rotations during idle segments represent deliberately imposed 8.96 and 18.04 kHz detuning hypotheses. These are **not** in the emitted candidate. The simulation evaluates all matched Y echo/sham pairs at 8 and 24 µs. This is a mechanism stress, not a calibrated forecast of the actual device. A fresh read-only inventory, validated native ISA and resource check would be needed for any physical run.

Run:

```sh
python research/arithmetic_holonomy_rotor/ibm_qpu_04b/compile_candidate.py --out /tmp/ahr04b-candidate
```

The archived Q4 receipts are unchanged. The new workflow retains generated QPY and manifest as a CI artifact, not an approved workload. All hardware remains HOLD.

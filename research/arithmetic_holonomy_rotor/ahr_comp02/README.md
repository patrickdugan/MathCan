# AHR-COMP-02

Sparse departures from the detuned Clifford/pi-flux arithmetic cube, following COMP-01. Read [AHR_COMP_02.md](AHR_COMP_02.md). The independent offline verifier checks parity lifting, sparse Gaussian/quartic decomposition, a three-qubit mixed-state-safe target-fidelity witness, the grouped measurement design and Gaussian branch expansion on a dense fixture.

```sh
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 python verify.py
```

`validation.json` is a deterministic local receipt (seed 20261124). The numerical oracle uses finite dense matrices; the scalable Gaussian-trajectory algorithm is a mathematical bound with phase-sensitive overlap as a dependency, not implemented at scale here. All hardware tests remain HOLD. No account access or submission code is included.

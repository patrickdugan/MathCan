# AHR-COMP-01

Read [the mathematical note](AHR_COMP_01.md) for compact gauge reconstruction, factorized fourth moments, circuit control/precision bounds, the parity-extended Gaussian baseline, and the exact counting reduction.

```sh
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 python verify.py --max-qubits 12 --output reproduced.json
OPENBLAS_NUM_THREADS=1 python verify.py --max-qubits 20 --output reproduced_20.json
```

The verifier is CPU-only and needs no IBM credentials. The second command is the full statevector benchmark; CI runs up to 12 qubits plus exact gauge reconstruction at 20 bits. See `LOCAL_RESULTS.md` for the recorded 20-qubit run. Timings are machine-specific. No Lean kernel proof, hardware experiment, or complexity separation is claimed.

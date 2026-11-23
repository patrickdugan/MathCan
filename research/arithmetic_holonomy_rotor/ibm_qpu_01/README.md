# AHR-QPU-01: signed holonomy on IBM Quantum, simulator-first

**Status (2026-11-23):** Local finite-dimensional verification passed. IBM circuit synthesis and hardware calibration are **unverified** in the current execution environment because Qiskit, Qiskit Aer and an IBM service credential were unavailable. QPU execution is explicitly gated. No QPU job was submitted.

This package implements the first hardware experiment proposed in AHR-01 and AHR-07, and creates an exact Q3 research handoff using AHR-08/09. Its independent dense oracle fixes little-endian qubit ordering, phase sign, return-probability scale and signed Fourier calibration.

## Offline run

```sh
python -m pip install -r requirements.txt
python -m pytest -q
python experiment.py                    # no account access
python run_benchmarks.py                 # writes receipts/offline_validation.json
```

### Qiskit-optional validation

```sh
python -m pip install -r requirements-qiskit.txt
python -m pytest -q tests/test_optional_qiskit.py
python experiment.py --mode compile_only # compares exact and Suzuki-2 synthesis
```

A run under GitHub CI also checks native two-qubit compilation into a CX/RZ/SX/X basis. The eventual physical compilation must target a real IBM backend and record layout, gate counts, calibration timestamps and shots. The exact two-qubit matrix is the reference for every build.

### Physical protocol

The Hamiltonian in the computational basis |00>, |10>, |01>, |11> is

\[
H_{\phi}=\log(2)N_x+\log(3)N_y+JX_x+J(1-N_x)X_y+JN_x(\cos\phi X_y+\sin\phi Y_y).
\]

Here x=q0 is the least-significant Qiskit bit and y=q1 is the second qubit. Choose J=1, t=1.6, phase reference theta=0.73, and offsets delta=(0,pi/2,pi,3pi/2). The injected theta is known during a controlled calibration experiment, but the estimator only uses its four measured counts plus a *separately calibrated* real first harmonic a1(t).

\[
Z_4=\tfrac12\sum_{j=0}^{3}P_{00}(t,\theta+\delta_j)e^{-i\delta_j},\quad
\hat\theta=\operatorname{wrap}[\arg(Z_4/a_1)].
\]

At t=1.6 the independent oracle gives a1=-0.25509419580938. Calibrating its negative sign is necessary for the correct phase orientation; the residual third-harmonic alias causes an approximately 0.000368 rad ideal phase shift for theta=0.73.

## Controls and comparisons

* Broken-cycle tree: delete edge (1,3), then check return probabilities are phase invariant.
* Reverse phase +/-0.73, plus zero flux and diagonal detuning control.
* Eight-point Fourier aliasing check, then four-point harmonic extraction.
* Equal TOTAL shot budget comparison against 64 edge-toggle/phase combinations.
* Conditional Bernoulli Fisher-information and local CRLB, with calibrated a1 and explicit nuisance models.
* Phenomenological independent readout-bit-flip and global-depolarization scenarios; **not** an Aer calibration substitute.
* Three-prime Q3: six addressable faces, three phase-controllable edges, 24 four-phase circuit/initial-state combinations, five independent chord phases, Bianchi residual and projection. Full Q3 Hamiltonian simulations are exact for eight states, while the O(t^2) local phase bias remains.

## Execution gates

Default is `simulation_only`. Local `compile_only` needs Qiskit but does not contact IBM. `dry_run` requires `--authorize-cloud`, a backend, and SDK support for the explicit `dry_run` argument. `hardware` requires `--authorize-cloud --authorize-qpu --backend NAME --instance OPEN_PLAN_CRN` plus explicit environment variables `AHR_QPU_ALLOW_LIVE_SUBMISSION=YES` and `AHR_QPU_FREE_PLAN_VERIFIED=YES` after checking that the backend and attached instance are on the free tier. The service is restricted to `plans_preference=["open"]`; the script NEVER switches to another backend or a paid fallback.

The current environment cannot access the Windows credential path `C:\\Users\\patri\\.qiskit\\qiskit-ibm.json`. Previous inspection showed it held `{}`. Nothing in this package exposes or records secrets.

Read [HARDWARE_GATE.md](HARDWARE_GATE.md) before cloud execution, and [RESULTS.md](RESULTS.md) for numerical results. The result is an engineered small quantum graph, not evidence of quantum speedup, RH consequences, or consciousness.

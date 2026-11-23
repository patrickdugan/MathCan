"""Replay a calibrated two-qubit Aer model and perturb two noise sources."""

from copy import deepcopy

import numpy as np
from qiskit_aer import AerSimulator
from qiskit_aer.noise import NoiseModel, QuantumError

SCENARIOS = {
    "calibrated_aer": (1.0, 1.0),
    "readout_half": (.5, 1.0),
    "readout_off": (0.0, 1.0),
    "two_qubit_half": (1.0, .5),
    "two_qubit_off": (1.0, 0.0),
}


def prepared_noise(snapshot, readout_scale, twoq_scale):
    model = NoiseModel()
    readout = [np.eye(2), np.eye(2)]
    for original in snapshot["compact_noise_model"]["errors"]:
        item = deepcopy(original)
        name, = item["operations"]
        if item["type"] == "roerror":
            if any(len(scope) != 1 for scope in item["gate_qubits"]):
                raise ValueError("correlated readout requires a different measurement model")
            transition = np.asarray(item["probabilities"])
            for (q,) in item["gate_qubits"]:
                readout[q] = np.eye(2) + readout_scale*(transition-np.eye(2))
            continue
        if name in {"cz", "cx", "ecr"}:
            if twoq_scale == 0:
                continue
            if twoq_scale < 1:
                item["instructions"] = [
                    [{"name": "id", "qubits": [0]}, {"name": "id", "qubits": [1]}],
                    *item["instructions"],
                ]
                item["probabilities"] = [1-twoq_scale, *(twoq_scale*p for p in item["probabilities"])]
        channel = QuantumError.from_dict(item)
        if "gate_qubits" in item:
            for qargs in item["gate_qubits"]:
                model.add_quantum_error(channel, name, qargs)
        else:
            model.add_all_qubit_quantum_error(channel, name)
    # Rightmost compact bit is q0. Rows are true states, columns measured states.
    readout_zero = np.kron(readout[1][:, 0], readout[0][:, 0])
    return model, readout_zero


def benchmark_noise(circuits, snapshot):
    saved = []
    for circuit in circuits:
        bare = circuit.remove_final_measurements(inplace=False)
        bare.save_probabilities([0, 1])
        saved.append(bare)
    result = {}
    for name, (readout, twoq) in SCENARIOS.items():
        noise_model, measured_zero = prepared_noise(snapshot, readout, twoq)
        simulator = AerSimulator(method="density_matrix", noise_model=noise_model, max_parallel_threads=2)
        observed = simulator.run(saved, shots=1, seed_simulator=271828).result()
        if not observed.success:
            raise RuntimeError(f"Aer density-matrix simulation failed for {name}")
        result[name] = [
            float(np.clip(np.asarray(observed.data(index)["probabilities"]) @ measured_zero, 0, 1))
            for index in range(len(saved))
        ]
    return result

"""Calibrated Aer density matrices and asymmetric readout convolution."""
import numpy as np
from qiskit_aer import AerSimulator
from qiskit_aer.noise import NoiseModel

from backend_snapshot import capture, rank_triples
from circuit_synthesis import compiled_probability, metrics, return_state
from q3_hamiltonian import ENERGIES


def historical_snapshot():
    from qiskit_ibm_runtime.fake_provider import FakeFez

    backend = FakeFez()
    triples = rank_triples(backend.target)
    reference = next((r for r in triples if r["contains_q2_pair"]), None)
    return {"mode": "historical_fake_provider", "account": None, "qpu_submitted": False,
            "devices": [{"backend": backend.name, "available_triples": len(triples),
                         "top_triples": triples[:5], "best_q2_pair_extension": reference}],
            "backend": capture(backend, triples[0])}


def quantum_instruction(instruction):
    """Restore AerJSONEncoder's [real, imaginary] pairs to matrix entries."""
    if instruction["name"] not in {"kraus", "unitary"}:
        return instruction
    params = np.asarray(instruction["params"])
    if params.ndim == 4 and params.shape[-1] == 2:
        params = params[..., 0] + 1j * params[..., 1]
    if params.ndim != 3:
        raise ValueError(f"invalid {instruction['name']} matrix parameters in snapshot")
    return {**instruction, "params": list(params)}


class CalibratedAer:
    def __init__(self, snapshot):
        entries = snapshot["noise"]["errors"]
        gate_errors = [
            {**entry, "instructions": [
                [quantum_instruction(instruction) for instruction in channel]
                for channel in entry["instructions"]
            ]}
            for entry in entries if entry["type"] != "roerror"
        ]
        self.simulator = AerSimulator(
            method="density_matrix", max_parallel_threads=1,
            noise_model=NoiseModel.from_dict({"errors": gate_errors}),
        )
        readout = {}
        for entry in entries:
            if entry["type"] == "roerror":
                for (qubit,) in entry["gate_qubits"]:
                    readout[qubit] = np.asarray(entry["probabilities"])
        if set(readout) != {0, 1, 2}:
            raise ValueError("missing local asymmetric readout model")
        self.channel = np.kron(readout[2], np.kron(readout[1], readout[0]))
        self.assignment_errors = [readout[q][0, 1] + readout[q][1, 0] for q in range(3)]

    def probabilities(self, circuits, cases):
        inputs = [c.remove_final_measurements(inplace=False) for c in circuits]
        for c in inputs:
            c.save_probabilities()
        results = self.simulator.run(inputs, shots=None).result()
        physical = np.array([results.data(i)["probabilities"] for i in range(len(inputs))])
        indices = np.array([return_state(c, setting.start) for c, setting in zip(circuits, cases)])
        return (physical @ self.channel)[np.arange(len(inputs)), indices]


def benchmark(phases, cases, method, target, snapshot, aer, magnitudes=1.0, energies=ENERGIES,
              keep_details=False):
    from circuit_synthesis import compile_cases
    from plaquette_estimator import probability

    circuits = compile_cases(phases, cases, method, target, magnitudes, energies)
    truth = probability(phases, cases, magnitudes, energies)
    compiled = np.array([compiled_probability(c, s) for c, s in zip(circuits, cases)])
    noisy = aer.probabilities(circuits, cases)
    rows = [metrics(c, target, snapshot) for c in circuits]
    answer = {"max_abs_probability_error": float(np.max(abs(compiled - truth))),
              "max_two_qubit_gates": max(r["two_qubit_gates"] for r in rows),
              "max_depth": max(r["depth"] for r in rows),
              "max_circuit_duration_s": max(r["critical_path_s"] for r in rows),
              "mean_noisy_abs_probability_error": float(np.mean(abs(noisy - truth))),
              "mean_binary_fidelity": float(np.mean(
                  (np.sqrt(noisy * truth) + np.sqrt((1-noisy) * (1-truth)))**2)),
              "total_two_qubit_gates": sum(r["two_qubit_gates"] for r in rows)}
    if keep_details:
        answer["per_setting"] = [{"case_id": case.id, "exact": float(p), "compiled": float(q),
                                  "aer": float(a), **row}
                                 for case, p, q, a, row in zip(cases, truth, compiled, noisy, rows)]
    return answer, circuits, compiled, noisy

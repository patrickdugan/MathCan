"""Compact Aer model with measured readout and explicit dwell relaxation."""
import numpy as np
from qiskit.circuit import Delay
from qiskit.quantum_info import Kraus, Operator, SuperOp
from qiskit.transpiler import PassManager
from qiskit_aer import AerSimulator
from qiskit_aer.noise import NoiseModel, QuantumError, RelaxationNoisePass

from circuits import logical_order

STRESS = {
    "nominal": (0., 1., 1., 0.),
    "extra_gate_error": (.25, 1., 1., 0.),
    "shorter_coherence_and_readout": (0., .80, 1.4, 0.),
    "coherent_coupler_shift": (0., 1., 1., .004),
}


def instruction(row):
    if row["name"] not in {"kraus", "unitary"}:
        return row
    params = np.asarray(row["params"])
    if params.ndim == 4 and params.shape[-1] == 2:
        params = params[..., 0] + 1j * params[..., 1]
    if params.ndim != 3:
        raise ValueError("invalid complex noise channel")
    return {**row, "params": list(params)}


def model(snapshot, stress):
    extra, coherence, readout_scale, angle = STRESS[stress]
    errors = [e for e in snapshot["noise"]["errors"] if e["type"] == "qerror"]
    decoded = [{**e, "instructions": [[instruction(op) for op in branch]
                                      for branch in e["instructions"]]} for e in errors]
    if extra or angle:
        # Rebuild public QuantumError objects from frozen channel payloads.
        gate_model = NoiseModel()
        for source in decoded:
            error = QuantumError.from_dict(source)
            if error.num_qubits == 2:
                channel = error.to_quantumchannel()
                if extra:
                    channel = (1-extra)*channel + extra*channel.compose(channel)
                if angle:
                    diagonal = np.diag(np.exp(1j * angle * np.array([1, -1, -1, 1])))
                    channel = channel.compose(SuperOp(Operator(diagonal)))
                error = QuantumError(Kraus(channel))
            if "gate_qubits" in source:
                for sites in source["gate_qubits"]:
                    gate_model.add_quantum_error(error, source["operations"], sites, warnings=False)
            else:
                gate_model.add_all_qubit_quantum_error(error, source["operations"], warnings=False)
    else:
        gate_model = NoiseModel.from_dict({"errors": decoded})
    readout = {}
    for source in snapshot["noise"]["errors"]:
        if source["type"] != "roerror":
            continue
        probabilities = np.asarray(source["probabilities"])
        for sites in source["gate_qubits"]:
            if len(sites) != 1:
                raise ValueError("this estimator requires single-qubit readout calibration")
            up = min(.499, probabilities[0, 1] * readout_scale)
            down = min(.499, probabilities[1, 0] * readout_scale)
            readout[sites[0]] = np.array([[1-up, up], [down, 1-down]])
    if len(readout) != 4:
        raise ValueError("four calibrated readout channels are required")
    channel = readout[3]
    for q in (2, 1, 0):
        channel = np.kron(channel, readout[q])
    t1, t2 = np.array(snapshot["coherence_s"]).T * coherence
    delay_pass = PassManager(RelaxationNoisePass(t1.tolist(), np.minimum(2*t1, t2).tolist(),
                                                 dt=snapshot["dt_s"], op_types=[Delay]))
    return AerSimulator(method="density_matrix", noise_model=gate_model,
                        max_parallel_threads=1), channel, delay_pass


def probabilities(circuits, snapshot, stress="nominal"):
    simulator, readout, delay_pass = model(snapshot, stress)
    inputs = [c.remove_final_measurements(inplace=False) for c in circuits]
    inputs = delay_pass.run(inputs, num_processes=1)
    for circuit in inputs:
        circuit.save_probabilities()
    execution = simulator.run(inputs, shots=None).result()
    return np.array([logical_order(np.array(execution.data(i)["probabilities"]) @ readout, circuit)
                     for i, circuit in enumerate(circuits)])

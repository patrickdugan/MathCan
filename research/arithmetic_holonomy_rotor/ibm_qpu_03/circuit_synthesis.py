"""Compile three-qubit evolution on the induced, dated backend target."""
from dataclasses import asdict

import numpy as np
from qiskit import ClassicalRegister, QuantumCircuit, transpile
from qiskit.circuit.library import PauliEvolutionGate, UCGate, get_standard_gate_name_mapping
from qiskit.quantum_info import SparsePauliOp, Statevector
from qiskit.synthesis import SuzukiTrotter
from qiskit.transpiler import InstructionProperties, Target
from scipy.linalg import expm

from q3_hamiltonian import EDGE_INDEX, ENERGIES, matrix

SEED = 902503
METHODS = ("exact", "exact-sabre3", "suzuki2-2", "suzuki2-4", "suzuki2-8",
           "suzuki4-1", "edge-2", "edge-4")
LIMITS = {"max_abs_probability_error": .015, "max_two_qubit_gates": 160,
          "max_circuit_duration_s": .00015}


def compact_target(snapshot):
    physical = snapshot["selection"]["physical_xyz"]
    isa = Target(num_qubits=3, dt=snapshot["dt_s"])
    gates = get_standard_gate_name_mapping()
    for name in sorted({row["gate"] for row in snapshot["instructions"]}):
        properties = {tuple(physical.index(q) for q in row["physical"]):
                      InstructionProperties(duration=row["duration_s"], error=row["error"])
                      for row in snapshot["instructions"] if row["gate"] == name}
        isa.add_instruction(gates[name], properties, name=name)
    return isa


def edge_layer(circuit, phases, magnitudes, axis, duration):
    controls = [q for q in range(3) if q != axis]
    blocks = []
    for value in range(4):
        u = sum(((value >> k) & 1) << q for k, q in enumerate(controls))
        edge = EDGE_INDEX[u, u ^ (1 << axis)]
        angle = duration * magnitudes[edge]
        off = -1j * np.sin(angle) * np.exp(1j * phases[edge])
        blocks.append(np.array([[np.cos(angle), off], [-off.conjugate(), np.cos(angle)]]))
    circuit.append(UCGate(blocks, up_to_diagonal=False), [axis, *controls])


def logical(phases, case, method, magnitudes=1.0, energies=ENERGIES):
    field = np.asarray(phases).copy()
    field[case.edge] += case.direction * case.offset
    h = matrix(field, magnitudes, energies)
    circuit = QuantumCircuit(3, name=case.id.replace(".", "p"))
    for q in range(3):
        if case.start >> q & 1:
            circuit.x(q)
    if method in ("exact", "exact-sabre3"):
        circuit.unitary(expm(-1j * case.time * h), range(3))
    elif method.startswith("edge-"):
        repetitions = int(method.split("-")[1])
        step = case.time / repetitions
        weights = np.broadcast_to(magnitudes, (12,))
        for _ in range(repetitions):
            for q, energy in enumerate(energies[[1, 2, 4]] - energies[0]):
                circuit.rz(step * energy / 2, q)
            for axis, fraction in ((0, .5), (1, .5), (2, 1), (1, .5), (0, .5)):
                edge_layer(circuit, field, weights, axis, step * fraction)
            for q, energy in enumerate(energies[[1, 2, 4]] - energies[0]):
                circuit.rz(step * energy / 2, q)
        expected = energies[0] + np.array([sum((u >> k & 1) * (energies[1 << k] - energies[0])
                                                  for k in range(3)) for u in range(8)])
        if not np.allclose(expected, energies):
            raise ValueError("edge product formula requires additive site energies")
    elif method.startswith("suzuki"):
        order = int(method[6])
        repetitions = int(method.split("-")[1])
        pauli = SparsePauliOp.from_operator(h, atol=1e-12)
        evolution = PauliEvolutionGate(pauli, time=case.time,
                                       synthesis=SuzukiTrotter(order=order, reps=repetitions))
        circuit.append(evolution, range(3))
    else:
        raise ValueError(f"unknown synthesis {method}")
    circuit.add_register(ClassicalRegister(3, "out"))
    circuit.measure(range(3), range(3))
    circuit.metadata = {"case_id": case.id, "setting": asdict(case), "synthesis": method}
    return circuit


def measure_map(circuit):
    pairs = {circuit.find_bit(item.clbits[0]).index: circuit.find_bit(item.qubits[0]).index
             for item in circuit.data if item.operation.name == "measure"}
    return [pairs[k] for k in range(3)]


def return_state(circuit, start):
    return sum(((start >> k) & 1) << q for k, q in enumerate(measure_map(circuit)))


def compile_cases(phases, cases, method, target, magnitudes=1.0, energies=ENERGIES):
    logical_circuits = [logical(phases, c, method, magnitudes, energies) for c in cases]
    routing, level = ("sabre", 3) if method == "exact-sabre3" else ("basic", 1)
    return transpile(logical_circuits, target=target, initial_layout=[0, 1, 2],
                     routing_method=routing, optimization_level=level,
                     seed_transpiler=SEED, num_processes=1)


def compiled_probability(circuit, case):
    p = Statevector.from_instruction(circuit.remove_final_measurements(inplace=False)).probabilities()
    return float(p[return_state(circuit, case.start)])


def metrics(circuit, target, snapshot):
    ends = [0.] * 3
    gate_counts = {}
    for item in circuit.data:
        name = item.operation.name
        qubits = tuple(circuit.find_bit(bit).index for bit in item.qubits)
        if len(qubits) == 2:
            gate_counts[name] = gate_counts.get(name, 0) + 1
        duration = target[name][qubits].duration
        if duration is None:
            raise ValueError(f"missing native duration for {name} on {qubits}")
        end = max(ends[q] for q in qubits) + duration
        for q in qubits:
            ends[q] = end
    physical = snapshot["selection"]["physical_xyz"]
    return {"depth": circuit.depth(), "native_two_qubit_gates": gate_counts,
            "two_qubit_gates": sum(gate_counts.values()), "critical_path_s": max(ends),
            "classical_bit_to_physical": [physical[q] for q in measure_map(circuit)]}


def physical_archive(circuit, snapshot):
    """Embed a validated compact ISA in the full backend-width register."""
    physical = snapshot["selection"]["physical_xyz"]
    result = QuantumCircuit(snapshot["backend_width"], name=circuit.name)
    result.add_register(ClassicalRegister(3, "out"))
    result.compose(circuit, qubits=physical, clbits=range(3), inplace=True)
    result.metadata = circuit.metadata.copy()
    return result

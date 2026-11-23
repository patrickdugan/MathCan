"""Three exact edge implementations and layout-preserving native compilation."""
from dataclasses import asdict
from itertools import pairwise

import numpy as np
from qiskit import ClassicalRegister, QuantumCircuit, transpile
from qiskit.circuit import Delay
from qiskit.circuit.library import RZGate, UCRZGate, UnitaryGate, get_standard_gate_name_mapping
from qiskit.quantum_info import Operator, Statevector
from qiskit.transpiler import InstructionProperties, Target

from model import B, Case, LABELS, edge_link, link_rotation, rotation, routes

METHODS = ("edge_block", "conditional", "multiplexed")
SEED = 381704


def compact_target(snapshot):
    physical = snapshot["selection"]["physical_xyz"]
    target = Target(num_qubits=4, dt=snapshot["dt_s"])
    gates = get_standard_gate_name_mapping()
    for name in sorted({row["gate"] for row in snapshot["instructions"]}):
        properties = {tuple(physical.index(q) for q in row["physical"]):
                      InstructionProperties(duration=row["duration_s"], error=row["error"])
                      for row in snapshot["instructions"] if row["gate"] == name}
        target.add_instruction(gates[name], properties, name=name)
    target.add_instruction(Delay(0, unit="dt"), {(q,): None for q in range(4)})
    return target


def append_link(circuit, u, v, axis, angle, method):
    if (u ^ v).bit_count() != 1:
        raise ValueError("link is not a cube edge")
    moving = (u ^ v).bit_length() - 1
    spectators = [q for q in range(3) if q != moving]
    if method == "edge_block" and angle:
        # Position bit is the low bit of this two-qubit block.
        block = np.zeros((4, 4), dtype=complex)
        a, b = ([0, 2], [1, 3]) if not (u >> moving & 1) else ([1, 3], [0, 2])
        value = rotation(axis, angle)
        block[np.ix_(b, a)], block[np.ix_(a, b)] = value, value.conj().T
        state = sum(((u >> q) & 1) << k for k, q in enumerate(spectators))
        circuit.append(UnitaryGate(block).control(2, ctrl_state=state), [*spectators, moving, 3])
        return
    if angle:
        if axis == "x":
            circuit.h(3)
        if method == "conditional":
            circuit.append(RZGate(-2 * angle).control(3, ctrl_state=u), [0, 1, 2, 3])
            circuit.append(RZGate(2 * angle).control(3, ctrl_state=v), [0, 1, 2, 3])
        elif method == "multiplexed":
            angles = [0.] * 8
            angles[u], angles[v] = -2 * angle, 2 * angle
            circuit.append(UCRZGate(angles), [3, 0, 1, 2])
        else:
            raise ValueError(f"unknown method {method}")
        if axis == "x":
            circuit.h(3)
    open_controls = [q for q in spectators if not (u >> q & 1)]
    for q in open_controls:
        circuit.x(q)
    circuit.ccx(*spectators, moving)
    for q in open_controls:
        circuit.x(q)


def logical(case, method, dt):
    circuit = QuantumCircuit(4, name=case.id.replace("/", "_"))
    circuit.metadata = {"case_id": case.id, "case": asdict(case), "method": method}
    if case.arm == "prepare":
        for q in range(4):
            if case.prepared >> q & 1:
                circuit.x(q)
    elif case.arm == "order_register":
        # Perfect classical label written into the same terminal Y basis.
        circuit.h(3)
        (circuit.sdg if case.label == "AB" else circuit.s)(3)
        add_dwell(circuit, case.dwell_us, dt)
    elif case.arm == "direct":
        for index, route in enumerate(routes(case)):
            if index:
                add_dwell(circuit, case.dwell_us, dt)
            axis, angle = ("z", case.beta) if route == B else ("x", case.alpha)
            circuit.unitary(rotation(axis, angle), [3])
            circuit.barrier(3)
    else:
        for order, route in enumerate(routes(case)):
            if order:
                add_dwell(circuit, case.dwell_us, dt)
            for u, v in pairwise(route):
                append_link(circuit, u, v, *link_rotation(case, u, v), method)
                circuit.barrier(range(4), label=f"edge_{order}_{u}_{v}")
    if case.arm != "prepare":
        circuit.sdg(3)
        circuit.h(3)
    circuit.add_register(ClassicalRegister(4, "out"))
    circuit.measure(range(4), range(4))
    return circuit


def add_dwell(circuit, dwell_us, dt):
    if dwell_us:
        circuit.delay(round(dwell_us * 1e-6 / dt), range(4), unit="dt")
        circuit.barrier(range(4))


def verify_links():
    max_delta = {}
    for method in METHODS:
        errors = []
        for u, v, axis, angle in ((1, 3, "x", .51), (5, 1, "z", -.7),
                                  (0, 1, "z", 0.), (5, 7, "x", -.24)):
            circuit = QuantumCircuit(4)
            append_link(circuit, u, v, axis, angle, method)
            errors.append(float(np.max(abs(
                Operator(circuit).data - edge_link(u, v, rotation(axis, angle))))))
        max_delta[method] = max(errors)
        assert max_delta[method] < 1e-12
    return max_delta


def verify_paths():
    """Check the intermediate vertex for each synthesized link separately."""
    records = {}
    for method in METHODS:
        task = {}
        for label in LABELS:
            state = Statevector.from_label("0000")
            case = Case(label, "signal", label)
            vertices = []
            for route in routes(case):
                for u, v in pairwise(route):
                    link = QuantumCircuit(4)
                    append_link(link, u, v, *link_rotation(case, u, v), method)
                    state = state.evolve(link)
                    vertices.append(v)
                    assert sum(state.probabilities()[[v, v+8]]) > 1-1e-11
            task[label] = vertices
        records[method] = task
    return records


def compile_cases(cases, method, snapshot, placement=(0, 1, 2, 3)):
    target = compact_target(snapshot)
    cs = [logical(case, method, snapshot["dt_s"]) for case in cases]
    sequence = transpile(cs, target=target, initial_layout=list(placement),
                         routing_method="sabre", optimization_level=3, seed_transpiler=SEED,
                         num_processes=1)
    return sequence, target


def measurement_map(circuit):
    assignment = {circuit.find_bit(item.clbits[0]).index: circuit.find_bit(item.qubits[0]).index
                  for item in circuit.data if item.operation.name == "measure"}
    return [assignment[i] for i in range(4)]


def logical_order(distribution, circuit):
    positions = measurement_map(circuit)
    ordering = [sum(((n >> q) & 1) << physical for q, physical in enumerate(positions))
                for n in range(16)]
    return np.asarray(distribution)[ordering]


def ideal_probability(circuit):
    unitary = QuantumCircuit(4)
    for item in circuit.data:
        if item.operation.name not in {"measure", "barrier", "delay"}:
            unitary.append(item.operation, [circuit.find_bit(q).index for q in item.qubits])
    state = Statevector.from_instruction(unitary)
    return logical_order(state.probabilities(), circuit)


def timing(circuit, target):
    ends = [0.] * 4
    totals = {}
    for item in circuit.data:
        name = item.operation.name
        qubits = tuple(circuit.find_bit(bit).index for bit in item.qubits)
        start = max(ends[q] for q in qubits)
        if name == "barrier":
            length = 0.
        elif name == "delay":
            length = item.operation.duration * target.dt
        else:
            length = target[name][qubits].duration
            if length is None:
                raise ValueError(f"missing duration for {name} on {qubits}")
            if len(qubits) == 2:
                totals[name] = totals.get(name, 0) + 1
        for q in qubits:
            ends[q] = start + length
    return {"native_depth": circuit.depth(lambda row: row.operation.name != "barrier"),
            "duration_s": max(ends), "active_end_s": ends, "native_two_qubit": totals,
            "two_qubit_count": sum(totals.values()),
            "preserved_edge_blocks": sum(bool(item.operation.label and
                                              item.operation.label.startswith("edge_"))
                                        for item in circuit.data if item.operation.name == "barrier")}


def physical_circuit(circuit, snapshot):
    result = QuantumCircuit(snapshot["backend_width"], name=circuit.name)
    result.add_register(ClassicalRegister(4, "out"))
    result.compose(circuit, qubits=snapshot["selection"]["physical_xyz"], clbits=range(4), inplace=True)
    result.metadata = circuit.metadata.copy()
    return result


def align_measurement(circuit, target, before_measure_s=None):
    """Synchronize the terminal measurement and optionally pad to a time floor."""
    result = circuit.copy_empty_like()
    for item in circuit.data:
        if item.operation.name != "measure":
            result.append(item.operation, [circuit.find_bit(q).index for q in item.qubits])
    active = timing(result, target)["duration_s"]
    result.barrier(range(4))
    padding = round(max(0., (before_measure_s or 0.) - active) / target.dt)
    if padding:
        result.delay(padding, range(4), unit="dt")
    result.measure(measurement_map(circuit), range(4))
    result.metadata = {**circuit.metadata, "terminal_pad_dt": padding}
    return result, active


def identity_audit(method, snapshot, placement):
    probe = QuantumCircuit(4)
    case = Case("identity_audit", "identity", "AB")
    for index, route in enumerate(routes(case)):
        for u, v in pairwise(route):
            append_link(probe, u, v, "z", 0., method)
            probe.unitary(np.eye(2), [3], label="explicit_internal_identity")
            probe.barrier(range(4), label=f"edge_{index}_{u}_{v}")
    target = compact_target(snapshot)
    compiled = transpile(probe, target=target, initial_layout=placement,
                         routing_method="sabre", optimization_level=3, seed_transpiler=SEED)
    return {"explicit_identity_before": int(probe.count_ops().get("unitary", 0)),
            "native_id_after": int(compiled.count_ops().get("id", 0)),
            "remaining_unitary_after": int(compiled.count_ops().get("unitary", 0)),
            "compiled_metrics": timing(compiled, target)}

"""Two-qubit synthesis and replayable calibration snapshots."""

from datetime import UTC, datetime
from importlib.metadata import version
from inspect import signature
from math import isfinite

import numpy as np
from qiskit import ClassicalRegister, QuantumCircuit, QuantumRegister
from qiskit.circuit import Measure, Parameter
from qiskit.circuit.library import (
    CXGate,
    CZGate,
    ECRGate,
    IGate,
    PauliEvolutionGate,
    RZGate,
    SXGate,
    XGate,
)
from qiskit.quantum_info import SparsePauliOp, Statevector
from qiskit.synthesis import SuzukiTrotter
from qiskit.transpiler import (
    InstructionProperties,
    Target,
    generate_preset_pass_manager,
)
from qiskit_aer import AerSimulator
from qiskit_aer.noise import NoiseModel
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2
from qiskit_ibm_runtime.executor_sampler import Sampler
from scipy.linalg import expm

from exact_oracle import harmonic, spectral_return
from hamiltonian import PRIMARY_TIME, square, square_paulis

SEED = 314159
P_TOL = 0.005
Z_TOL = 0.005
METHODS = ("exact", "suzuki_2", "suzuki_4", "suzuki_8")


def now():
    return datetime.now(UTC).isoformat(timespec="seconds")


def gate_dictionary():
    return {
        "id": IGate(), "rz": RZGate(Parameter("a")), "sx": SXGate(), "x": XGate(),
        "cz": CZGate(), "cx": CXGate(), "ecr": ECRGate(), "measure": Measure(),
    }


def _calibrated(prop):
    return prop is not None and prop.error is not None and isfinite(prop.error) and 0 <= prop.error < 1


def capture(backend, *, account=None, live=False):
    """Select an adjacent pair, reduce the ISA and NoiseModel, and redact account metadata."""
    target = backend.target
    choices = []
    for name in ("cz", "ecr", "cx"):
        if name not in target:
            continue
        for pair, properties in target[name].items():
            if pair is None or not _calibrated(properties):
                continue
            readout = [target["measure"].get((q,)) for q in pair]
            if all(_calibrated(item) for item in readout):
                choices.append((3*properties.error + sum(item.error for item in readout), pair, name))
    if not choices:
        raise ValueError("no adjacent pair with native two-qubit and readout calibrations")
    score, pair, native = min(choices)
    instructions = []
    for operation in sorted(set(gate_dictionary()) & set(target.operation_names)):
        for qargs, properties in target[operation].items():
            if qargs and set(qargs).issubset(pair):
                instructions.append({
                    "gate": operation, "physical": qargs,
                    "duration_s": None if properties is None else properties.duration,
                    "error": None if properties is None else properties.error,
                })
    model = NoiseModel.from_backend(backend).to_dict(serializable=True)
    selected = []
    for item in model["errors"]:
        if "gate_qubits" not in item:
            selected.append(item)
            continue
        local = [tuple(pair.index(q) for q in scope) for scope in item["gate_qubits"] if set(scope).issubset(pair)]
        if local:
            selected.append({**item, "gate_qubits": local})
    properties = backend.properties()
    if SamplerV2 is not Sampler:
        raise RuntimeError("requires the client-side SamplerV2 default from Runtime >=0.52")
    return {
        "target_type": "live_snapshot" if live else "archived_backend",
        "captured_utc": now(), "backend": backend.name, "backend_width": backend.num_qubits,
        "dt_s": target.dt, "physical_pair_xy": pair, "native_pair_interaction": native, "pair_score": score,
        "calibration_id": getattr(backend, "calibration_id", None),
        "calibration_timestamp": properties.last_update_date.isoformat() if properties else None,
        "backend_version": backend.backend_version, "instructions": instructions,
        "qubits": [
            {"physical": q, "t1_s": target.qubit_properties[q].t1, "t2_s": target.qubit_properties[q].t2,
             "readout_error": target["measure"][(q,)].error} for q in pair
        ],
        "compact_noise_model": {"errors": selected}, "account": account,
        "sdk": {"service": str(signature(QiskitRuntimeService)), "sampler_run": str(signature(SamplerV2.run)),
                "implementation": SamplerV2.__module__},
        "versions": {name: version(name) for name in ("numpy", "scipy", "qiskit", "qiskit-aer", "qiskit-ibm-runtime")},
    }


def compact_target(snapshot):
    pair = list(snapshot["physical_pair_xy"])
    target = Target(num_qubits=2, dt=snapshot["dt_s"])
    gates = gate_dictionary()
    for gate in sorted({row["gate"] for row in snapshot["instructions"]}):
        properties = {
            tuple(pair.index(q) for q in row["physical"]): InstructionProperties(
                duration=row["duration_s"], error=row["error"],
            )
            for row in snapshot["instructions"] if row["gate"] == gate
        }
        target.add_instruction(gates[gate], properties, name=gate)
    return target


def logical(case, method):
    h = square(case.phase, case.energy, case.mask)
    pauli = SparsePauliOp.from_list(square_paulis(case.phase, case.energy, case.mask))
    np.testing.assert_allclose(h, pauli.to_matrix(), atol=2e-13, rtol=0)
    circuit = QuantumCircuit(2, name=case.id.replace(".", "p"))
    circuit.metadata = {"case_id": case.id}
    if method == "exact":
        circuit.unitary(expm(-1j*case.time*h), [0, 1])
    else:
        repetitions = int(method.rsplit("_", 1)[-1])
        formula = SuzukiTrotter(order=2, reps=repetitions, preserve_order=True)
        circuit.append(PauliEvolutionGate(pauli, time=case.time, synthesis=formula), [0, 1])
    circuit.add_register(ClassicalRegister(2, "out"))
    circuit.measure([0, 1], [0, 1])
    return circuit


def measurements(circuit):
    mapping = {
        circuit.find_bit(item.clbits[0]).index: circuit.find_bit(item.qubits[0]).index
        for item in circuit.data if item.operation.name == "measure"
    }
    return mapping[0], mapping[1]


def metrics(circuit, target):
    assert measurements(circuit) == (0, 1)
    total = 0.
    two = 0
    missing = set()
    for item in circuit.data:
        operation = item.operation.name
        qargs = tuple(circuit.find_bit(bit).index for bit in item.qubits)
        if not target.instruction_supported(operation_name=operation, qargs=qargs):
            raise ValueError(f"Non-ISA instruction {operation} on {qargs}")
        if len(qargs) == 2:
            two += 1
        prop = target[operation].get(qargs)
        if prop is not None and prop.duration is not None:
            total += prop.duration
        elif operation != "rz":
            missing.add(operation)
    return {"depth": circuit.depth(), "two_qubit_gates": two, "serial_duration_s": total,
            "unknown_duration_gates": sorted(missing)}


def ideal_aer(circuits):
    work = []
    for circuit in circuits:
        bare = circuit.remove_final_measurements(inplace=False)
        bare.save_probabilities([0, 1])
        work.append(bare)
    simulator = AerSimulator(method="statevector", max_parallel_threads=2)
    result = simulator.run(work, shots=1, seed_simulator=271828).result()
    if not result.success:
        raise RuntimeError("Aer ideal simulation failed")
    return [float(result.data(i)["probabilities"][0]) for i in range(len(circuits))]


def grouped(cases, probabilities):
    by_id = {}
    for case, value in zip(cases, probabilities, strict=True):
        key = f"{case.arm}_t{case.time:.1f}"
        by_id.setdefault(key, [None] * 4)[case.quadrant] = value
    return by_id


def benchmark(cases, snapshot):
    target = compact_target(snapshot)
    exact = [spectral_return(square(case.phase, case.energy, case.mask), case.time) for case in cases]
    reference = grouped(cases, exact)[f"signal_t{PRIMARY_TIME:.1f}"]
    suites, summary, predictions = {}, {}, {}
    for method in METHODS:
        manager = generate_preset_pass_manager(
            optimization_level=3, target=target, initial_layout=[0, 1], routing_method="none",
            seed_transpiler=SEED, approximation_degree=1.0,
        )
        logicals = [logical(case, method) for case in cases]
        compiled = manager.run(logicals, num_processes=1)
        entries = [metrics(circuit, target) for circuit in compiled]
        compiled_p = ideal_aer(compiled)
        logical_p = [float(Statevector.from_instruction(
            # Expand PauliEvolutionGate so Statevector uses the selected product formula.
            circuit.remove_final_measurements(inplace=False).decompose(),
        ).probabilities()[0]) for circuit in logicals]
        np.testing.assert_allclose(compiled_p, logical_p, atol=8e-11, rtol=0)
        error = max(abs(np.asarray(compiled_p)-exact))
        z_error = abs(harmonic(grouped(cases, compiled_p)[f"signal_t{PRIMARY_TIME:.1f}"])-harmonic(reference))
        summary[method] = {
            "sum_depth": sum(row["depth"] for row in entries),
            "max_depth": max(row["depth"] for row in entries),
            "sum_two_qubit_gates": sum(row["two_qubit_gates"] for row in entries),
            "max_absolute_probability_error": float(error),
            "primary_absolute_harmonic_error": float(z_error),
            "eligible": bool(error <= P_TOL and z_error <= Z_TOL),
        }
        suites[method] = compiled
        predictions[method] = [
            {**case.record(), **entry, "p_exact": p, "p_uncompiled_statevector": sv, "p_compiled_ideal_aer": ia}
            for case, entry, p, sv, ia in zip(cases, entries, exact, logical_p, compiled_p, strict=True)
        ]
    eligible = [method for method in METHODS if summary[method]["eligible"]]
    if not eligible:
        raise RuntimeError("no synthesis passed the fixed accuracy thresholds")
    chosen = min(eligible, key=lambda method: tuple(summary[method][key] for key in (
        "sum_depth", "max_depth", "sum_two_qubit_gates", "max_absolute_probability_error",
    )))
    return chosen, suites[chosen], summary, predictions


def embed(compact, snapshot):
    physical = QuantumCircuit(
        QuantumRegister(snapshot["backend_width"], "q"), ClassicalRegister(2, "out"),
        name=compact.name, metadata=compact.metadata,
    )
    pair = tuple(snapshot["physical_pair_xy"])
    physical.compose(compact, qubits=pair, clbits=[0, 1], inplace=True)
    if measurements(physical) != pair:
        raise ValueError("physical readout mapping is inconsistent with the snapshot")
    return physical

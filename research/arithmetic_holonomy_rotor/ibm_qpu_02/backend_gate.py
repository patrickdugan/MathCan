"""AHR-QPU-02: historical fake-backend ISA/noise gate and read-only IBM inventory.

Default mode stays offline. The optional metadata-only mode never submits jobs.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import numpy as np

SOURCE = Path(__file__).resolve().parents[1] / "ibm_qpu_01"
if not SOURCE.is_dir():
    SOURCE = Path(__file__).resolve().parents[1] / "ahr_qpu_01"
sys.path.insert(0, str(SOURCE))
from circuit_synthesis import build_circuit
from exact_oracle import PHASE_OFFSETS, four_phase_probabilities
from phase_estimator import quadrature, wrap

SEED = 20261123


def candidate_pairs(backend):
    """Rank native directed links by two-qubit and readout snapshot errors."""
    props = backend.properties()
    native = []
    for operation in ("cz", "ecr", "cx"):
        if operation not in backend.operation_names:
            continue
        for edge in backend.coupling_map.get_edges():
            u, v = map(int, edge)
            try:
                error = float(props.gate_error(operation, [u, v]))
                r0 = float(props.readout_error(u))
                r1 = float(props.readout_error(v))
            except (AttributeError, LookupError, ValueError, TypeError):
                continue
            if not all(np.isfinite([error, r0, r1])):
                continue
            native.append({"pair": [u, v], "operation": operation,
                           "two_qubit_error": error, "readout_errors": [r0, r1],
                           "heuristic_score": error + (r0 + r1) / 4})
    return sorted(native, key=lambda p: (p["heuristic_score"], p["pair"]))


def statevector_p00(circuit):
    from qiskit.quantum_info import Statevector
    bare = circuit.remove_final_measurements(inplace=False)
    return float(abs(Statevector.from_instruction(bare).data[0]) ** 2)


def compile_four(backend, pair, phases, method="exact", reps=4,
                 broken=False, t=1.6, seed=SEED):
    from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
    pm = generate_preset_pass_manager(backend=backend, initial_layout=list(pair),
                                     optimization_level=2, seed_transpiler=seed)
    raw = [build_circuit(t, float(phi), method=method, reps=reps,
                         broken=broken, measure=True) for phi in phases]
    compiled = pm.run(raw)
    return [compiled] if not isinstance(compiled, list) else compiled


def circuit_metrics(circuits, native_gate):
    return [{"depth": int(c.depth()),
             "two_qubit_count": int(sum(1 for instruction in c.data
                                        if len(instruction.qubits) == 2)),
             "native_count": int(c.count_ops().get(native_gate, 0)),
             "ops": {k: int(v) for k, v in c.count_ops().items()},
             "num_qubits": int(c.num_qubits)} for c in circuits]


def shots_p00(result, index, shots):
    counts = result.get_counts(index)
    successes = sum(int(number) for bitstring, number in counts.items()
                    if int(bitstring.replace(" ", ""), 2) == 0)
    return successes / shots


def wrapped_error(x, y):
    return float(wrap(x - y))


def bootstrap_phase(primary_p, reference_p, shots, reps=1000, seed=SEED):
    """Sampling-only uncertainty; excludes calibration drift and model mismatch."""
    rng = np.random.default_rng(seed)
    primary = rng.binomial(shots, primary_p, size=(reps, 4)) / shots
    reference = rng.binomial(shots, reference_p, size=(reps, 4)) / shots
    return np.asarray(wrap(np.angle(quadrature(primary) / quadrature(reference))))


def local_mock_audit(shots=2048, theta=.73, t=1.6, seed=SEED, output=None):
    """Run the historical FakeManilaV2 snapshot, never a live device."""
    from qiskit_ibm_runtime.fake_provider import FakeManilaV2
    from qiskit_aer import AerSimulator

    backend = FakeManilaV2()
    pairs = candidate_pairs(backend)
    if not pairs:
        raise RuntimeError("Snapshot lacks a calibrated two-qubit pair")
    selected = pairs[0]
    pair = selected["pair"]
    exact = four_phase_probabilities(t, theta)
    synthesis = []
    for method, reps in (("exact", 0), ("suzuki2", 4)):
        isa = compile_four(backend, pair, theta + PHASE_OFFSETS,
                           method=method, reps=reps, t=t, seed=seed)
        metrics = circuit_metrics(isa, selected["operation"])
        errors = [abs(statevector_p00(c) - reference)
                  for c, reference in zip(isa, exact)]
        synthesis.append({"method": method, "reps": reps,
                          "max_ideal_p00_error": float(max(errors)),
                          "max_2q_gate_count": max(z["two_qubit_count"] for z in metrics),
                          "max_depth": max(z["depth"] for z in metrics),
                          "metrics": metrics})
    acceptable = [s for s in synthesis if s["max_ideal_p00_error"] < .015]
    if not acceptable:
        raise RuntimeError("No synthesis candidate satisfies P00 error budget")
    selected_synthesis = min(
        acceptable, key=lambda x: (x["max_2q_gate_count"], x["max_depth"],
                                   x["max_ideal_p00_error"]))
    method, reps = selected_synthesis["method"], selected_synthesis["reps"]
    phases = [theta + PHASE_OFFSETS, PHASE_OFFSETS, theta + PHASE_OFFSETS]
    circuits = []
    for block, phasevec in enumerate(phases):
        circuits += compile_four(backend, pair, phasevec, method=method,
                                 reps=reps, broken=(block == 2), t=t, seed=seed)
    simulator = AerSimulator.from_backend(backend)
    result = simulator.run(circuits, shots=shots, seed_simulator=seed).result()
    p = np.array([shots_p00(result, i, shots) for i in range(len(circuits))])
    main_p, reference_p, broken_p = p.reshape(3, 4)
    z = quadrature(main_p)
    z_ref = quadrature(reference_p)
    if abs(z) < 1e-6 or abs(z_ref) < 1e-6:
        raise RuntimeError("Insufficient quadrature signal in mock backend")
    estimate = float(wrap(np.angle(z / z_ref)))
    draws = bootstrap_phase(main_p, reference_p, shots, seed=seed)
    errors = np.asarray(wrap(draws - theta))
    ci = np.quantile(np.asarray(wrap(draws - estimate)), [.025, .975])
    all_metrics = circuit_metrics(circuits, selected["operation"])
    report = {
        "status": "PASS", "evidence": "historical_fake_backend_snapshot_only",
        "backend": backend.name, "backend_qubits": int(backend.num_qubits),
        "snapshot_properties_last_update": str(backend.properties().last_update_date),
        "selected_pair": selected, "synthesis_comparison": synthesis,
        "selected_method": {"method": method, "reps": reps},
        "theta_true": float(theta), "theta_estimate": estimate,
        "angular_error_deg": float(np.degrees(wrapped_error(estimate, theta))),
        "sampling_ci_deg_around_estimate": list(map(float, np.degrees(ci))),
        "bootstrap_rmse_to_true_deg": float(np.degrees(np.sqrt(np.mean(errors ** 2)))),
        "observed_probabilities": {
            "primary": main_p.tolist(), "zero_phase_reference": reference_p.tolist(),
            "broken_cycle": broken_p.tolist()},
        "broken_cycle_phase_spread": float(np.max(broken_p) - np.min(broken_p)),
        "shots_per_circuit": int(shots), "circuit_count": len(circuits),
        "total_shots": int(len(circuits) * shots),
        "isa_worst_depth": max(c["depth"] for c in all_metrics),
        "isa_worst_2q_gates": max(c["two_qubit_count"] for c in all_metrics),
        "isa_metrics": all_metrics,
        "verified_open_plan": False, "account_allocation_checked": False,
        "live_backend_calibration_checked": False, "hardware_submission": False,
        "report_explanation": "Historical fake snapshot, not a live QPU."
    }
    if output:
        Path(output).parent.mkdir(parents=True, exist_ok=True)
        Path(output).write_text(json.dumps(report, indent=2) + "\n")
    return report


def read_only_inventory(instance, authorized, output=None):
    """Explicitly authorized account metadata lookup with no Sampler/job creation."""
    if not authorized or not instance:
        raise RuntimeError("Read-only inspection needs --authorize-cloud and --instance")
    from qiskit_ibm_runtime import QiskitRuntimeService
    service = QiskitRuntimeService(instance=instance, plans_preference=["open"])
    devices = []
    for backend in service.backends(operational=True, simulator=False):
        pairs = candidate_pairs(backend)
        devices.append({"name": backend.name, "num_qubits": backend.num_qubits,
                        "best_pair": pairs[0] if pairs else None,
                        "calibration_date": str(backend.properties().last_update_date)})
    report = {"mode": "read_only_inventory", "devices": devices,
              "instance_supplied": True, "open_plan_verified": False,
              "remaining_allocation_verified": False, "job_submitted": False,
              "instruction": "Confirm plan and remaining RUs in IBM Platform dashboard."}
    if output:
        Path(output).parent.mkdir(parents=True, exist_ok=True)
        Path(output).write_text(json.dumps(report, indent=2) + "\n")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["fake", "read-only-inventory"], default="fake")
    parser.add_argument("--shots", type=int, default=2048)
    parser.add_argument("--theta", type=float, default=.73)
    parser.add_argument("--time", type=float, default=1.6)
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--instance", help="Existing IBM instance name or CRN")
    parser.add_argument("--authorize-cloud", action="store_true")
    parser.add_argument("--output", default="receipts/fake_backend_report.json")
    args = parser.parse_args()
    if args.shots < 1 or args.time <= 0:
        parser.error("Shots and time must be positive")
    if args.mode == "fake":
        ret = local_mock_audit(shots=args.shots, theta=args.theta, t=args.time,
                               seed=args.seed, output=args.output)
    else:
        ret = read_only_inventory(args.instance, args.authorize_cloud, output=args.output)
    print(json.dumps({k: v for k, v in ret.items()
                      if k not in ("isa_metrics", "synthesis_comparison")}, indent=2))


if __name__ == "__main__":
    main()

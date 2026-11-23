"""Execute the offline routed-order circuit study and archive its exact workload."""
import argparse
from dataclasses import asdict
from hashlib import sha256
from importlib.metadata import version
import json
from math import ceil
from pathlib import Path

import numpy as np
from qiskit import qpy

from calibration import historical, write_json
from circuits import (METHODS, SEED, align_measurement, compile_cases, ideal_probability,
                      identity_audit, measurement_map, physical_circuit, timing, verify_links,
                      verify_paths)
from endpoints import (JOINT_FLOOR, SAMPLING_SEED, SHOTS, SYSTEMATIC, commuting_interval,
                       from_counts, model_endpoints, primary_interval)
from model import Case, LABELS, STRESS_ANGLE_SEED, Y, audit, cases, oracle
from noise import STRESS, probabilities

SPEC_COMMIT = "27a60fe7654531b6775f6a543fe42fdd8d0868d8"
PLACEMENTS = ((0, 1, 2, 3), (0, 1, 3, 2), (1, 2, 3, 0))
ORDER_SEED = 228341


def pad(circuits, planned, target):
    active = [align_measurement(c, target)[1] for c in circuits]
    standard = max(t for case, t in zip(planned, active) if case.id.startswith("signal/"))
    return [align_measurement(c, target, None if case.arm == "prepare"
                              else standard + case.dwell_us * 1e-6)[0]
            for c, case in zip(circuits, planned)]


def bakeoff(snapshots, quick):
    four_methods = METHODS if not quick else ("multiplexed",)
    placements = PLACEMENTS if not quick else PLACEMENTS[:1]
    samples = [Case(f"signal/{label}", "signal", label) for label in LABELS]
    results = []
    for index, snapshot in enumerate(snapshots):
        for method in four_methods:
            for placement in placements:
                compiled, target = compile_cases(samples, method, snapshot, placement)
                compiled = pad(compiled, samples, target)
                metrics = [timing(c, target) for c in compiled]
                exact = [model_endpoints(ideal_probability(c), s.label) for c, s in zip(compiled, samples)]
                assert all(v["joint_correct_and_return"] > 1-1e-10 for v in exact)
                assert all(m["preserved_edge_blocks"] == 8 for m in metrics)
                noisy = [model_endpoints(p, s.label) for p, s in zip(
                    probabilities(compiled, snapshot), samples)]
                results.append({"snapshot_index": index, "method": method, "placement": list(placement),
                                "ideal": exact, "aer": noisy, "native_metrics": metrics,
                                "selection_worst_label_joint": min(x["joint_correct_and_return"] for x in noisy),
                                "selection_two_qubit_total": sum(m["two_qubit_count"] for m in metrics)})
    winner = min(results, key=lambda row: (-row["selection_worst_label_joint"],
                                           row["selection_two_qubit_total"]))
    return results, winner


def assessment(planned, p, stress_index):
    streams = np.random.SeedSequence([SAMPLING_SEED, stress_index]).spawn(2)
    rng, prep_rng = [np.random.default_rng(s) for s in streams]
    rows = {}
    for case, probabilities_ in zip(planned, p, strict=True):
        normalized = np.maximum(probabilities_, 0.)
        normalized /= normalized.sum()
        counts = (prep_rng if case.arm == "prepare" else rng).multinomial(SHOTS, normalized)
        row = {"probabilities": normalized.tolist(), "counts": counts.tolist()}
        if case.arm == "prepare":
            row["correct_readout_probability"] = float(normalized[case.prepared])
        else:
            row["expected"] = model_endpoints(normalized, case.label)
            row["sampled"] = from_counts(counts, case.label)
        rows[case.id] = row
    primary = [rows[f"signal/{label}"] for label in LABELS]
    sampled_interval = primary_interval([row["sampled"] for row in primary])
    pair = [rows[f"commuting/{label}"] for label in LABELS]
    zero = commuting_interval(*pair)
    mean = float(np.mean([row["expected"]["joint_correct_and_return"] for row in primary]))
    signs = [row["expected"]["conditional_Y"] for row in primary]
    return {"primary_joint_mean": mean, "primary_joint_95_with_allowance": sampled_interval,
            "primary_Y_by_label": signs, "commuting_difference_95_with_allowance": zero,
            "passes": bool(mean >= JOINT_FLOOR and sampled_interval[0] >= JOINT_FLOOR
                           and signs[0] < 0 < signs[1] and zero[0] <= 0 <= zero[1]), "rows": rows}


def manifests(out, compiled, planned, target, snapshot, inventory, theoretical, assessments, winner):
    order = np.random.default_rng(ORDER_SEED).permutation(len(planned))
    circuits = [physical_circuit(compiled[i], snapshot) for i in order]
    layout = snapshot["selection"]["physical_xyz"]
    records = []
    nominal = assessments["nominal"]["rows"]
    for i in order:
        s, c = planned[i], compiled[i]
        mean = nominal[s.id]
        records.append({"case": asdict(s), "shots": SHOTS,
                        "measurement_by_classical_bit": [layout[q] for q in measurement_map(c)],
                        "terminal_pad_dt": c.metadata["terminal_pad_dt"],
                        "metrics": timing(c, target), "ideal_distribution": theoretical[i].tolist(),
                        "expected_outcome_probabilities": mean["probabilities"],
                        "predicted": mean.get("expected")})
    bundle = out / "q4_candidate_isa.qpy"
    with bundle.open("wb") as stream:
        qpy.dump(circuits, stream)
    rep_delay = snapshot["rep_delay_s"]
    timing_known = rep_delay is not None
    emitted_s = sum((row["metrics"]["duration_s"] + (rep_delay or .00025)) * SHOTS for row in records)
    nominal_cost = 15 + emitted_s
    provisional_cap = ceil(2 * nominal_cost)
    account = inventory["account"]
    free_gate = bool(account and account["free_qpu_seconds"] >= provisional_cap and timing_known)
    sim_gate = all(x["passes"] for x in assessments.values())
    return {"study": "AHR-QPU-04", "spec_commit": SPEC_COMMIT,
            "hardware_decision": "HOLD", "qpu_submitted": False, "job_approval": False,
            "simulation_gate": "PASS" if sim_gate else "FAIL",
            "free_plan_resource_gate": "PROVISIONAL_FIT" if free_gate else "HOLD",
            "backend": snapshot["backend"], "calibration_timestamp": snapshot["calibration_timestamp"],
            "calibration_id": snapshot["calibration_id"], "operational_snapshot": inventory["source"],
            "verified_account": account, "physical_qubits": layout,
            "initial_physical_by_logical": [layout[k] for k in winner["placement"]],
            "synthesis_method": winner["method"], "transpiler_seed": SEED,
            "randomized_order_seed": ORDER_SEED, "shots": sum(row["shots"] for row in records),
            "circuit_count": len(circuits), "default_rep_delay_s": rep_delay,
            "modeled_shot_time_s": emitted_s, "fixed_overhead_assumption_s": 15,
            "estimated_usage_s": nominal_cost, "provisional_max_seconds": provisional_cap,
            "cap_rule": "ceil(2 * (shot-weighted duration plus repetition delay plus 15 seconds))",
            "qpy_sha256": sha256(bundle.read_bytes()).hexdigest(),
            "snapshot_sha256": sha256((out / "calibration.json").read_bytes()).hexdigest(),
            "cases": records}


def run(inventory, out, *, quick=False):
    out.mkdir(parents=True, exist_ok=True)
    write_json(out / "calibration.json", inventory)
    exact = audit()
    exact["link_synthesis_full_space_max_error"] = verify_links()
    exact["verified_synthesis_path_vertices"] = verify_paths()
    suite, winning = bakeoff(inventory["snapshots"][:1] if quick else inventory["snapshots"], quick)
    write_json(out / "compilation.json", {"candidates": suite, "selected": winning})
    print("Selected", winning["method"], winning["placement"], winning["selection_worst_label_joint"], flush=True)
    snapshot = inventory["snapshots"][winning["snapshot_index"]]
    exact["identity_compilation_audit"] = identity_audit(
        winning["method"], snapshot, winning["placement"])
    planned = cases()[:18] if quick else cases()
    raw, target = compile_cases(planned, winning["method"], snapshot, winning["placement"])
    cooked = pad(raw, planned, target)
    ideal = np.array([ideal_probability(c) for c in cooked])
    for c, s, p in zip(cooked, planned, ideal, strict=True):
        if s.arm not in {"prepare", "direct", "order_register"}:
            assert timing(c, target)["preserved_edge_blocks"] == 8
            internal = oracle(s)[1]
            y = (internal.conj() @ Y @ internal).real
            np.testing.assert_allclose(p[[0, 8]], [(1+y)/2, (1-y)/2], atol=1e-10, rtol=0)
    before = probabilities(raw, snapshot)
    plan = {}
    for index, name in enumerate(STRESS):
        print("Simulating", name, len(cooked), "circuits", flush=True)
        plan[name] = assessment(planned, probabilities(cooked, snapshot, name), index)
    for i, case in enumerate(planned):
        nominal_row = plan["nominal"]["rows"][case.id]
        nominal_row["unpadded_expectation"] = (float(before[i, case.prepared]) if case.arm == "prepare"
                                               else model_endpoints(before[i], case.label))
        nominal_row["unpadded_metrics"] = timing(raw[i], target)
    document = manifests(out, cooked, planned, target, snapshot, inventory, ideal, plan, winning)
    write_json(out / "simulation.json", {"oracle": exact, "stress_parameters": STRESS, "scenarios": plan,
                                        "shots_per_case": SHOTS, "systematic_probability_allowance": SYSTEMATIC,
                                        "holdout_angle_seed": STRESS_ANGLE_SEED,
                                        "training_cases": ["signal/AB", "signal/BA"],
                                        "versions": {p: version(p) for p in (
                                            "numpy", "scipy", "qiskit", "qiskit-aer", "qiskit-ibm-runtime")}})
    write_json(out / "manifest.json", document)
    print("Simulation gate", document["simulation_gate"], "Hardware HOLD", flush=True)
    return document


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--calibration", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--quick", action="store_true")
    args = p.parse_args()
    inventory = json.loads(args.calibration.read_text(encoding="utf-8")) if args.calibration else historical()
    run(inventory, args.out, quick=args.quick)


if __name__ == "__main__":
    main()

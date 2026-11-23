"""Offline sensitivity of the frozen joint prediction to recorded readout changes."""
import argparse
from copy import deepcopy
from pathlib import Path

import numpy as np

from calibration import write_json
from endpoints import model_endpoints
from hardware_execution import compact_circuits, inputs, read
from noise import probabilities


def replay_readout(receipts):
    hardware = receipts / "hardware"
    manifest, _, circuits = inputs(receipts)
    preflight = read(hardware / "preflight.json")["current_target"]
    calibration = read(hardware / "calibration_comparison.json")
    start = calibration["job_start_values"]
    reweighted = deepcopy(preflight)
    rows = []
    for error in reweighted["noise"]["errors"]:
        if error["type"] != "roerror":
            rows.append(error)
            continue
        for (q,) in error["gate_qubits"]:
            physical = manifest["physical_qubits"][q]
            up, down = start[f"q{physical}/assignment_errors"]
            rows.append({**error, "gate_qubits": [[q]], "probabilities": [[1-up, up], [down, 1-down]]})
    reweighted["noise"]["errors"] = rows
    local = compact_circuits(circuits, manifest, preflight)
    primary = [(row["case"], circuit) for row, circuit in zip(manifest["cases"], local, strict=True)
               if row["case"]["id"] in {"signal/AB", "signal/BA"}]
    p = probabilities([circuit for _, circuit in primary], reweighted)
    forecasts = {case["id"]: model_endpoints(row, case["label"])
                 for (case, _), row in zip(primary, p, strict=True)}
    return {"job_id": calibration["job_id"], "method": "post hoc assignment-matrix substitution in Aer",
            "changed_model_inputs": "single-qubit readout matrices only",
            "job_start_calibration": calibration["job_start_calibration"],
            "cases": forecasts, "primary_joint_mean": float(np.mean([
                r["joint_correct_and_return"] for r in forecasts.values()]))}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--receipts", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    report = replay_readout(args.receipts)
    write_json(args.output, report)
    print(f"Readout-updated joint forecast: {report['primary_joint_mean']:.6f}")


if __name__ == "__main__":
    main()

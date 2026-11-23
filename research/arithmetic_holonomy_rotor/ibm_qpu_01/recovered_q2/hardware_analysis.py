"""Reproduce the hardware-only analysis from archived counts and simulations."""

import argparse
from pathlib import Path

import numpy as np

from exact_oracle import harmonic
from experiment import load, write
from phase_estimator import acceptance, complex_record, estimate, rectangle


def summarize(manifest, scans, hardware):
    counts = hardware["counts"]
    shots = hardware["shots_per_circuit"]
    if len(manifest["case_order"]) != 36 or len(set(manifest["case_order"])) != 36 or shots != 2048:
        raise ValueError("the approved hardware workload requires 36 cases at 2,048 shots")
    if set(counts) != set(manifest["case_order"]):
        raise ValueError("hardware cases differ from the registered workload")
    if any(set(values).difference({"00", "01", "10", "11"}) or sum(values.values()) != shots
           for values in counts.values()):
        raise ValueError("hardware outcome labels or shots do not match the plan")
    groups = {}
    for case in manifest["cases"]:
        name = f'{case["arm"]}_t{case["time"]:.1f}'
        groups.setdefault(name, [None]*4)[case["quadrant"]] = counts[case["id"]].get("00", 0)
    if any(None in values for values in groups.values()):
        raise ValueError("a four-offset group is incomplete")

    details = {}
    for name, values in sorted(groups.items()):
        probabilities = np.asarray(values)/shots
        results = {
            "counts_00": values, "observed_probabilities": probabilities.tolist(),
            "exact_probabilities": scans["exact"][name],
            "calibrated_aer_probabilities": scans["calibrated_aer"][name],
            "observed_harmonic": complex_record(harmonic(probabilities)),
            "exact_harmonic": complex_record(harmonic(scans["exact"][name])),
            "calibrated_aer_harmonic": complex_record(harmonic(scans["calibrated_aer"][name])),
            "raw_joint_95_rectangle": rectangle(values, shots),
        }
        if name.startswith(("signal_", "reversed_")):
            reference = groups["reference_"+name.rsplit("_", 1)[1]]
            results["reference_calibrated_phase"] = estimate(values, reference, shots)
        details[name] = results
    primary = manifest["primary"]["signal"]
    result = acceptance(
        groups[primary], shots, harmonic(scans["exact"][primary]),
        [rows[primary] for name, rows in scans.items() if name not in {"exact", "compiled_ideal"}],
    )
    saved = hardware.get("primary_acceptance")
    if saved is not None and saved != result:
        raise ValueError("recomputed acceptance differs from the collected result")
    tree = next(row for name, row in details.items() if name.startswith("tree_"))
    tree_rectangle = tree["raw_joint_95_rectangle"]
    return {
        "job_id": hardware["job_id"], "counts_source": "IBM Quantum hardware",
        "shots_per_circuit": shots, "shots_total": len(counts)*shots,
        "primary_group": primary, "primary_acceptance": result, "four_phase_groups": details,
        "tree_rectangle_contains_origin": all(
            tree_rectangle[axis][0] <= 0 <= tree_rectangle[axis][1] for axis in ("real", "imag")
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("run", type=Path)
    args = parser.parse_args()
    path = args.run
    result = summarize(
        load(path / "manifest.json"), load(path / "q2_protocol.json")["scans"],
        load(path / "hardware_counts.json"),
    )
    write(path / "hardware_analysis.json", result)
    print(f"Verified and analyzed {result['shots_total']:,} hardware shots.")


if __name__ == "__main__":
    main()

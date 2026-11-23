"""Replay the approved Q4 hardware pilot from its raw computational counts."""
import argparse
import json
from pathlib import Path

import numpy as np

from calibration import write_json
from endpoints import (JOINT_FLOOR, commuting_interval, from_counts,
                       model_endpoints, primary_interval, wilson)
from model import LABELS


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def replay(manifest, recorded, refreshed=None):
    expected_order = [r["case"]["id"] for r in manifest["cases"]]
    if len(expected_order) != len(set(expected_order)) or list(recorded["counts"]) != expected_order:
        raise ValueError("IBM return ledger differs from the ordered circuit manifest")
    rows = {}
    for index, setting in enumerate(manifest["cases"]):
        case = setting["case"]
        name = case["id"]
        raw = recorded["counts"][name]
        if (sum(raw.values()) != setting["shots"] or
                any(len(k) != 4 or set(k) - {"0", "1"} or
                    not isinstance(v, int) or v < 0 for k, v in raw.items())):
            raise ValueError(f"invalid counts for {name}")
        counts = [raw.get(format(k, "04b"), 0) for k in range(16)]
        predicted = (refreshed["nominal"][index] if refreshed
                     else setting["expected_outcome_probabilities"])
        result = {"counts": counts, "shots": setting["shots"],
                  "case": case, "expected_outcome_probabilities": predicted}
        if case["arm"] == "prepare":
            successes = counts[case["prepared"]]
            result |= {"correct_prepared": successes / setting["shots"],
                       "correct_prepared_wilson_95": wilson(successes, setting["shots"])}
        else:
            result |= {"observed": from_counts(counts, case["label"]),
                       "calibrated_aer": model_endpoints(np.asarray(predicted), case["label"])}
        rows[name] = result
    primary = {label: rows[f"signal/{label}"]["observed"] for label in LABELS}
    joint_ci = primary_interval(list(primary.values()))
    mean = float(np.mean([r["joint_correct_and_return"] for r in primary.values()]))
    commuting = commuting_interval(*(rows[f"commuting/{label}"] for label in LABELS))
    contrast = (rows["commuting/AB"]["observed"]["return_and_positive_Y"] -
                rows["commuting/BA"]["observed"]["return_and_positive_Y"])
    signs = primary["AB"]["conditional_Y"] < 0 < primary["BA"]["conditional_Y"]
    prep = min(row["correct_prepared"] for row in rows.values() if "correct_prepared" in row)
    return {"job_id": recorded["job_id"], "shots": sum(row["shots"] for row in rows.values()),
            "pub_case_ids_match": recorded["pub_case_ids_match"], "primary_by_label": primary,
            "primary_mean_joint": mean, "primary_joint_95_with_allowance": joint_ci,
            "expected_Y_signs": signs,
            "commuting_joint_positive_Y_AB_minus_BA": contrast,
            "commuting_difference_95_with_allowance": commuting,
            "clears_simulation_design_threshold_on_hardware":
            bool(mean >= JOINT_FLOOR and joint_ci[0] >= JOINT_FLOOR and signs
                 and commuting[0] <= 0 <= commuting[1]),
            "minimum_preparation_and_readout_success": prep, "cases": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--hardware", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    current = args.hardware / "refreshed_simulation.json"
    result = replay(read(args.manifest), read(args.hardware / "counts.json"),
                    read(current) if current.exists() else None)
    write_json(args.output, result)


if __name__ == "__main__":
    main()

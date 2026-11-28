"""Independent standard-library arithmetic audit for the ROC-04A paper postscript.

Source rows were copied byte-for-byte from merged LoopedTransformers PR #155:
experiments/roc04_permutation_transfer/ROC04A_PRIMARY_BY_SEED.csv
Original Git blob: 0c5e1b23f1d85808e3b4f3d593a0024e86702d3b

Scientific scope: six independent model initializations on one previously
exposed 256-rule development pool; ROC-04 reserved evaluation remains sealed.
"""
from __future__ import annotations

import csv
import hashlib
import itertools
import json
import math
from pathlib import Path
from statistics import mean

HERE = Path(__file__).resolve().parent
ROWS = HERE / "ROC04A_primary_six_seed_v01.csv"
SOURCE_BLOB = "0c5e1b23f1d85808e3b4f3d593a0024e86702d3b"
SEEDS = (2026111705, 2026111707, 2026111711,
         2026111713, 2026111717, 2026111719)
DEV_N = 256


def verify(path: Path = ROWS) -> dict:
    raw = path.read_bytes()
    blob = hashlib.sha1(f"blob {len(raw)}".encode() + bytes([0]) + raw).hexdigest()
    if blob != SOURCE_BLOB:
        raise AssertionError(f"source CSV changed: {blob}")
    with path.open(newline="", encoding="utf-8") as fh:
        data = list(csv.DictReader(fh))
    if tuple(int(r["seed"]) for r in data) != SEEDS:
        raise AssertionError("incomplete or reordered six-seed family")
    if any(int(r["dev_cases"]) != DEV_N for r in data):
        raise AssertionError("dev sample count changed")
    differences = []
    for r in data:
        low = int(r["low_correct"])
        high = int(r["high_correct"])
        whole = int(r["high_whole_table_correct"])
        if not (0 <= low <= DEV_N and 0 <= high <= DEV_N
                and 0 <= whole <= DEV_N):
            raise AssertionError("invalid integer case count")
        for count, key in ((low,"low_accuracy"),
                           (high,"high_accuracy"),
                           (whole,"high_whole_table_accuracy")):
            if abs(count/DEV_N-float(r[key])) > 1e-14:
                raise AssertionError(f"published {key} count mismatch")
        d = (high-low)/DEV_N
        if abs(d-float(r["paired_gain"])) > 1e-14:
            raise AssertionError("paired gain disagrees with counted cases")
        for field in ("high_legal_row_swap_accuracy",
                      "high_nuisance_prediction_stability"):
            if not (0 <= float(r[field]) <= 1):
                raise AssertionError(f"invalid {field}")
        differences.append(high-low)

    observed = sum(differences)
    flips = [
        sum(s*d for s,d in zip(signs,differences))
        for signs in itertools.product((-1,1),repeat=len(SEEDS))
    ]
    extreme = sum(v >= observed for v in flips)
    p = extreme/len(flips)
    positive = sum(d>0 for d in differences)
    mean_low = sum(int(r["low_correct"]) for r in data)/(DEV_N*len(SEEDS))
    mean_high = sum(int(r["high_correct"]) for r in data)/(DEV_N*len(SEEDS))
    mean_gain = observed/(DEV_N*len(SEEDS))
    mean_whole = sum(int(r["high_whole_table_correct"]) for r in data)/(DEV_N*len(SEEDS))
    mean_swap = mean(float(r["high_legal_row_swap_accuracy"]) for r in data)
    mean_stability = mean(float(r["high_nuisance_prediction_stability"]) for r in data)
    task_seeds = sum(int(r["high_correct"])/DEV_N >= .70 for r in data)
    table_seeds = sum(int(r["high_whole_table_correct"])/DEV_N >= .50 for r in data)
    primary = positive>=5 and mean_gain>=.20 and p<=.05
    competence = task_seeds>=5 and table_seeds>=5
    result = {
        "study": "ROC-04A exact six-seed development permutation-transfer",
        "model_seeds": len(data),
        "dev_cases_per_model": DEV_N,
        "mean_low_accuracy": mean_low,
        "mean_high_accuracy": mean_high,
        "mean_accuracy_gain": mean_gain,
        "positive_paired_seeds": positive,
        "one_sided_exact_signflip_numerator": extreme,
        "one_sided_exact_signflip_denominator": len(flips),
        "one_sided_exact_signflip_p": p,
        "primary_gate": "PASS" if primary else "FAIL",
        "high_dev_task_at_least_70pct_seeds": task_seeds,
        "high_full_eight_row_at_least_50pct_seeds": table_seeds,
        "mean_high_whole_table_exact": mean_whole,
        "competence_gate": "PASS" if competence else "FAIL",
        "high_legal_swap_accuracy": mean_swap,
        "high_nuisance_invariance_eligible": mean_stability,
        "roc04_reserved_test_evaluated": False,
        "roc02_sealed_families_evaluated": False,
        "scope": "exposed development permutations, separate from 384 reserved identities",
    }
    assert mean_low == 352/1536
    assert mean_high == 1086/1536
    assert mean_gain == 734/1536
    assert mean_whole == 171/1536
    assert (positive,extreme,len(flips)) == (6,1,64)
    assert (task_seeds,table_seeds) == (4,0)
    assert primary and not competence
    assert abs(mean_swap - 0.7376302083333334) < 1e-12
    assert abs(mean_stability - 0.9253393665158373) < 1e-12
    return result


if __name__ == "__main__":
    print(json.dumps(verify(),sort_keys=True,indent=2))

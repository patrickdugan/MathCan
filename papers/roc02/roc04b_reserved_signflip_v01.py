"""Independent ROC-04B reserved-test six-seed arithmetic audit, stdlib only.

The CSV is an exact Git blob copy of the published LoopedTransformers result:
MoralityLabAI/LoopedTransformers PR #157, merged at 6ca6ae0.
Full original model/test JSONL and 4,608 predictions are in the separately
SHA-256-pinned ROC04B hosted reproducibility archive.
"""
from __future__ import annotations

import csv
import hashlib
import itertools
import json
from pathlib import Path
from statistics import mean

HERE = Path(__file__).resolve().parent
CSV = HERE / "ROC04B_reserved_test_by_seed_v01.csv"
SOURCE_GIT_BLOB = "3b0d1907c56385bacb61cfff8c3075faf153b5e4"
SEEDS = (2026111705, 2026111707, 2026111711,
         2026111713, 2026111717, 2026111719)
TEST_SIZE = 384


def audit(csv_path: Path = CSV) -> dict:
    raw = csv_path.read_bytes()
    blob = hashlib.sha1(f"blob {len(raw)}".encode() + bytes([0]) + raw).hexdigest()
    if blob != SOURCE_GIT_BLOB:
        raise AssertionError("ROC-04B result CSV differs from original merged Git blob")
    with csv_path.open(newline="", encoding="utf-8") as fp:
        rows = list(csv.DictReader(fp))
    if tuple(int(x["seed"]) for x in rows) != SEEDS:
        raise AssertionError("expected all six frozen model seeds in order")

    diffs = []
    total_low = total_high = total_table = 0
    task_pass = table_pass = 0
    for item in rows:
        if int(item["test_examples"]) != TEST_SIZE:
            raise AssertionError("test sample cardinality changed")
        low = int(item["low_correct"])
        high = int(item["high_correct"])
        table = int(item["high_complete_table_count"])
        if not all(0 <= v <= TEST_SIZE for v in (low, high, table)):
            raise AssertionError("incorrect number of answers/tables")
        for count, key in (
            (low, "low_accuracy"),
            (high, "high_accuracy"),
            (table, "high_complete_table_rate"),
        ):
            if abs(count/TEST_SIZE-float(item[key])) > 1e-14:
                raise AssertionError("raw count and published rate disagree")
        diff = high-low
        if abs(diff/TEST_SIZE-float(item["high_minus_low"])) > 1e-14:
            raise AssertionError("published paired effect disagree")
        total_low += low
        total_high += high
        total_table += table
        diffs.append(diff)
        task_pass += high/TEST_SIZE >= 0.70
        table_pass += table/TEST_SIZE >= 0.50

    observed = sum(diffs)
    flips = [
        sum(sign*d for sign,d in zip(signs,diffs))
        for signs in itertools.product((-1,1), repeat=len(SEEDS))
    ]
    extreme = sum(outcome >= observed for outcome in flips)
    p = extreme/len(flips)
    positive_seeds = sum(d > 0 for d in diffs)
    paired_gain = observed/(TEST_SIZE*len(SEEDS))
    primary_pass = positive_seeds>=5 and paired_gain>=0.20 and p<=0.05
    competence_pass = task_pass>=5 and table_pass>=5
    assert (total_low,total_high,total_table)==(486,1683,274)
    assert (positive_seeds,extreme,len(flips))==(6,1,64)
    assert (task_pass,table_pass)==(4,0)
    assert paired_gain==0.51953125
    assert primary_pass and not competence_pass
    result = {
        "study": "ROC-04B frozen twelve-model reserved 384-permutation confirmation",
        "frozen_model_seed_count": 6,
        "models_scored": 12,
        "new_reserved_test_records": TEST_SIZE,
        "total_correct_low": total_low,
        "total_correct_high": total_high,
        "total_complete_tables_high": total_table,
        "mean_low_accuracy": total_low/(TEST_SIZE*len(SEEDS)),
        "mean_high_accuracy": total_high/(TEST_SIZE*len(SEEDS)),
        "mean_high_complete_table_accuracy": total_table/(TEST_SIZE*len(SEEDS)),
        "mean_paired_gain": paired_gain,
        "positive_seed_count": positive_seeds,
        "one_sided_exact_signflip_extreme": extreme,
        "signflip_assignments": len(flips),
        "one_sided_exact_signflip_p": p,
        "primary_gate": "PASS" if primary_pass else "FAIL",
        "task_70pct_seed_count": task_pass,
        "whole_table_50pct_seed_count": table_pass,
        "competence_gate": "PASS" if competence_pass else "FAIL",
        "new_training_updates_during_test": 0,
        "original_roc02_sealed_families_6_7_evaluated": False,
        "caveat": "Same six ROC04A model initializations; new reserved table IDs, one fixed generator family",
    }
    return result


if __name__ == "__main__":
    print(json.dumps(audit(), sort_keys=True, indent=2))

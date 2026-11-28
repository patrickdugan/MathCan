"""ROC-02 v0.1 primary six-seed exact randomization audit (stdlib only).

The six values are copied from original ROC-02E model-seed paired summary
on calibration source families 4/5. This reports a descriptive test because
observer hyperparameters were selected using the same calibration family.
Run: python papers/roc02/roc02_primary_signflip_v01.py
"""
from __future__ import annotations

import csv
import itertools
import json
import math
from pathlib import Path
from statistics import mean, stdev

ROOT = Path(__file__).resolve().parent
T_CRIT_DF5_975 = 2.570581835636305  # t_{5,0.975} for a descriptive interval
EXPECTED_SEEDS = (2026111601, 2026111603, 2026111607,
                  2026111609, 2026111613, 2026111619)

def audit(path: Path = ROOT / "ROC02_primary_six_seed_v01.csv") -> dict:
    with path.open(newline="") as f:
        rows = list(csv.DictReader(f))
    keys = tuple(int(r["seed"]) for r in rows)
    if keys != EXPECTED_SEEDS:
        raise ValueError("Unexpected seed order or count")
    effects = [float(row["joint_minus_task"]) for row in rows]
    if not all(math.isfinite(x) for x in effects):
        raise ValueError("Nonfinite paired effects")
    observed = mean(effects)
    outcomes = [
        mean(s * v for s, v in zip(signs, effects))
        for signs in itertools.product((-1, 1), repeat=6)
    ]
    ge = sum(x >= observed - 1e-14 for x in outcomes)
    p = ge / len(outcomes)
    halfwidth = T_CRIT_DF5_975 * stdev(effects) / math.sqrt(6)
    result = {
        "study": "ROC-02E preregistered calibration-only primary",
        "six_initializations": 6,
        "positive_seed_count": sum(x > 0 for x in effects),
        "mean_joint_minus_task": observed,
        "one_sided_signflip_numerators": ge,
        "signflip_total": len(outcomes),
        "one_sided_signflip_p": p,
        "descriptive_t95_interval": [observed-halfwidth, observed+halfwidth],
        "inferential_scope": "Exposed calibration family reused for gamma selection; descriptive",
        "sealed_test_evaluated": False,
    }
    assert result["positive_seed_count"] == 3
    assert abs(observed - 0.0001414833510959094) < 1e-15
    assert p == .375
    assert abs((observed-halfwidth) - (-.001011)) < 2e-6
    assert abs((observed+halfwidth) - (.001294)) < 2e-6
    return result

if __name__ == "__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))

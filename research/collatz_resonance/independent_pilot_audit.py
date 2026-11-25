"""Independent arithmetic/selection audit of the COL-03 saved pilot.

Run from the repository root:
  python -m research.collatz_resonance.independent_pilot_audit --check

The direct search uses modular powers, rather than the lattice representation,
to find every candidate for d <= 313. For larger parameters this audit checks
feasibility and reruns the arithmetic selector, without re-enumerating targets.
Existing cycle-target receipts remain a separate source of evidence.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path
from statistics import median

from .arithmetic import branch_lattice
from .pilot_controls import alternative
from .resonance_pilot import CONFIG, predict_pair

BASE = Path(__file__).parent
OUTPUT = BASE / "data/independent_pilot_audit.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def brute_best(d: int, unit_states: int, slope: int | None) -> tuple[int, int, int]:
    """Independent candidate search with direct 2**A == 3**u (mod d).

    For the cone-only arm, every attainable exponent residue has period
    ord_d(2) <= phi(d) <= d-1; searching through 2*u+d therefore includes
    its first solution above the lower endpoint.
    """
    best = None
    for u in range(1, unit_states + 1):
        if slope is None:
            lower, upper = 2 * u, 2 * u + d
        else:
            width = isqrt(22 * u)
            lower, upper = max(2 * u, slope * u - width), slope * u + width
        triple_residue = pow(3, u, d)
        for A in range(lower, upper + 1):
            if pow(2, A, d) == triple_residue:
                candidate = (A + 2 * u, u, A)
                if best is None or candidate < best:
                    best = candidate
    if best is None:
        raise AssertionError(f"no direct-search candidate for d={d}, slope={slope}")
    return best


def run() -> dict:
    source = BASE / "data/resonance_pilot.csv"
    rows = list(csv.DictReader(source.open()))
    summary = json.loads((BASE / "data/resonance_pilot.json").read_text())
    controls = json.loads((BASE / "data/pilot_controls.json").read_text())
    source_hashes = {
        name: digest(BASE / name) for name in (
            "arithmetic.py", "collatz_core.py", "resonance_pilot.py", "pilot_controls.py")
    }
    for key, name in (("source_sha256", "resonance_pilot.py"),
                      ("core_sha256", "collatz_core.py"),
                      ("arithmetic_sha256", "arithmetic.py")):
        if summary[key] != source_hashes[name]:
            raise AssertionError(f"pilot source hash mismatch: {name}")
    if controls["pilot_csv_sha256"] != digest(source):
        raise AssertionError("control receipt targets a different pilot CSV")
    expected = {}
    for split, bounds in (("development", CONFIG["development_d"]),
                          ("evaluation", CONFIG["evaluation_d"])):
        expected[split] = [d for d in range(bounds[0], bounds[1] + 1, 4) if gcd(d, 6) == 1]
        if [int(row["d"]) for row in rows if row["split"] == split] != expected[split]:
            raise AssertionError("split roster is incomplete, duplicated, or out of order")
    if set(expected["development"]) & set(expected["evaluation"]):
        raise AssertionError("parameter splits overlap")

    brute_primary = brute_controls = 0
    for row in rows:
        d, N = int(row["d"]), int(row["unit_states"])
        if N != sum(gcd(n, d) == 1 for n in range(1, d + 1, 2)):
            raise AssertionError("unit-state feature disagrees with arithmetic count")
        u, A = int(row["predicted_u"]), int(row["predicted_A"])
        if not (1 <= u <= N and A >= 2 * u and (A - 6 * u) ** 2 <= 22 * u):
            raise AssertionError("candidate violates primary search constraints")
        if pow(2, A, d) != pow(3, u, d):
            raise AssertionError("candidate violates direct modular equation")
        if int(row["predicted_period"]) != A + 2 * u:
            raise AssertionError("candidate period conversion differs")
        if predict_pair(branch_lattice(d), N) != (u, A):
            raise AssertionError("selector replay differs from saved pair")
        actual = Fraction(row["observed_median_period"])
        error = abs(Fraction(A + 2 * u) - actual) / actual
        if abs(float(error) - float(row["lattice_relative_absolute_error"])) > 0.500001e-9:
            raise AssertionError("saved primary relative error differs")
        if d <= 313:
            if brute_best(d, N, 6) != (A + 2 * u, u, A):
                raise AssertionError("independent primary minimum differs")
            brute_primary += 1
            for slope in (4, 8, None):
                if brute_best(d, N, slope) != alternative(d, N, slope):
                    raise AssertionError("independent control minimum differs")
                brute_controls += 1

    # Recompute the principal evaluation summaries directly from exact ratios.
    evaluation = [row for row in rows if row["split"] == "evaluation"]
    primary_errors = []
    size_errors = []
    for row in evaluation:
        actual = Fraction(row["observed_median_period"])
        primary_errors.append(abs(Fraction(row["predicted_period"]) - actual) / actual)
        # The CSV size predictor was rounded to nine places; keep that precision
        # visible and compare aggregate medians to a 1e-9 tolerance.
        size_errors.append(abs(Fraction(row["size_prediction"]) - actual) / actual)
    recomputed = {
        "parameters": len(evaluation),
        "primary_median_relative_absolute_error": round(float(median(primary_errors)), 9),
        "size_median_relative_absolute_error_from_rounded_predictions": round(float(median(size_errors)), 9),
        "primary_strict_wins_from_rounded_size_predictions": sum(a < b for a, b in zip(primary_errors, size_errors)),
        "cycles_with_predicted_pair": sum(int(row["cycles_with_predicted_pair"]) for row in evaluation),
        "unit_cycles": sum(int(row["unit_cycles"]) for row in evaluation),
    }
    original = summary["summaries"]["evaluation"]
    if abs(recomputed["primary_median_relative_absolute_error"] - original["median_relative_absolute_error_lattice_covered"]) > 1e-9:
        raise AssertionError("primary median changed")
    if abs(recomputed["size_median_relative_absolute_error_from_rounded_predictions"] - original["median_relative_absolute_error_size_same_covered"]) > 1e-9:
        raise AssertionError("size median changed")
    if recomputed["primary_strict_wins_from_rounded_size_predictions"] != original["lattice_strict_wins_on_covered"]:
        raise AssertionError("primary win count changed")
    for key in ("cycles_with_predicted_pair", "unit_cycles"):
        if recomputed[key] != original[key]:
            raise AssertionError(f"evaluation aggregate changed: {key}")

    return {
        "schema": "mathcan.collatz.independent-pilot-audit.v1",
        "status": "passed",
        "evidence_class": "exact finite arithmetic and receipt audit",
        "source_sha256": digest(Path(__file__)),
        "audited_source_sha256": source_hashes,
        "pilot_csv_sha256": digest(source),
        "pilot_summary_sha256": digest(BASE / "data/resonance_pilot.json"),
        "controls_summary_sha256": digest(BASE / "data/pilot_controls.json"),
        "all_primary_candidates_checked": len(rows),
        "arithmetic_unit_counts_checked": len(rows),
        "primary_minima_checked_by_direct_modular_search": brute_primary,
        "control_minima_checked_by_direct_modular_search": brute_controls,
        "brute_search_max_parameter": 313,
        "evaluation_summary_recomputed": recomputed,
        "scope": "Target cycle census is inherited from the separately replayed pilot receipt. Direct candidate optimality is independently exhausted through d=313; larger rows receive feasibility and selector replay checks.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    result = run()
    if args.check:
        if result != json.loads(args.output.read_text()):
            raise SystemExit("independent audit receipt differs")
    else:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: result[key] for key in (
        "status", "all_primary_candidates_checked", "primary_minima_checked_by_direct_modular_search",
        "control_minima_checked_by_direct_modular_search")}))


if __name__ == "__main__":
    main()

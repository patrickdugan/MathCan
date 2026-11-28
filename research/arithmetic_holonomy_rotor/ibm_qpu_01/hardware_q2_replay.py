#!/usr/bin/env python3
"""Offline-only reconstruction of IBM Q2 raw-count results; Python stdlib only."""
from __future__ import annotations
import cmath
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent / "receipts" / "hardware_q2"
EXPECTED_JOB = "dc1vksqnj2vs73dfu0n0"

def read(name: str):
    return json.loads((ROOT / name).read_text(encoding="utf-8"))

def harmonic(counts, arm: str, t: str = "1.6", shots: int = 2048) -> complex:
    p = [counts[f"{arm}_t{t}_q{q}"].get("00", 0) / shots for q in range(4)]
    return complex((p[0] - p[2]) / 2, (p[3] - p[1]) / 2)

def wrap_radians(x: float) -> float:
    return (x + math.pi) % (2 * math.pi) - math.pi

def validate() -> dict:
    result = read("hardware_counts.json")
    manifest = read("manifest.json")
    usage = read("post_run_allocation.json")
    execution = read("execution_evidence.json")
    analysis = read("hardware_analysis.json")
    shots = result["shots_per_circuit"]
    counts = result["counts"]

    assert result["job_id"] == EXPECTED_JOB == execution["job_id"] == analysis["job_id"]
    assert result["status"] == "DONE"
    assert result["backend"] == manifest["backend"] == "ibm_fez"
    assert manifest["physical_pair_xy"] == [9, 10]
    assert shots == 2048 and len(counts) == len(manifest["case_order"]) == 36
    assert len(set(manifest["case_order"])) == 36 and set(manifest["case_order"]) == set(counts)
    for values in counts.values():
        assert set(values) <= {"00", "01", "10", "11"}
        assert sum(values.values()) == shots
        assert all(isinstance(v, int) and v >= 0 for v in values.values())

    total = len(counts) * shots
    assert total == 73728
    assert result["qpu_seconds"] == 21
    assert result["free_balance_checked"]["remaining_qpu_seconds"] == 536
    assert usage["remaining_qpu_seconds"] == 515
    assert abs(536 - 21 - 515) < 1e-9
    assert manifest["qpy_sha256"] == hashlib.sha256((ROOT / "q2_isa.qpy").read_bytes()).hexdigest()
    cal = (ROOT / "calibration.json").read_text(encoding="utf-8")
    assert manifest["calibration_sha256"] == hashlib.sha256(cal.encode("utf-8")).hexdigest()
    assert execution["pub_metadata_matches_manifest"]
    assert execution["calibration_at_job_start"] == execution["calibration_at_last_chunk"]
    assert len(execution["chunks"]) == 1 and sorted(execution["chunks"][0]["pubs"]) == list(range(36))

    signal = harmonic(counts, "signal")
    reference = harmonic(counts, "reference")
    reversed_signal = harmonic(counts, "reversed")
    tree = harmonic(counts, "tree")
    forward_deg = math.degrees(cmath.phase(signal / reference))
    reverse_deg = math.degrees(cmath.phase(reversed_signal / reference))

    assert abs(signal.real - (-0.154296875)) < 1e-12
    assert abs(signal.imag - (-0.19873046875)) < 1e-12
    assert abs(forward_deg - 38.903662164070035) < 1e-8
    assert abs(reverse_deg - (-42.85997335229036)) < 1e-8
    assert abs(tree) < 0.02
    assert abs(wrap_radians(math.radians(forward_deg) - 0.73)) < 0.1
    assert abs(wrap_radians(math.radians(reverse_deg) + 0.73)) < 0.1
    assert analysis["tree_rectangle_contains_origin"]
    assert analysis["primary_acceptance"]["passes"]

    return {"job_id": EXPECTED_JOB, "backend": "ibm_fez", "physical_qubits": [9, 10],
            "circuits": len(counts), "shots_per_circuit": shots, "total_shots": total,
            "forward_deg": forward_deg, "reverse_deg": reverse_deg,
            "signal_harmonic": [signal.real, signal.imag],
            "tree_harmonic": [tree.real, tree.imag],
            "free_qpu_seconds": 21, "remaining_seconds_as_reported": 515,
            "status": "OFFLINE_REPLAY_PASS"}

if __name__ == "__main__":
    print(json.dumps(validate(), indent=2))

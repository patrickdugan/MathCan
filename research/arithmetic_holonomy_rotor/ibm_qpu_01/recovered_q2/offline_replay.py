"""Replay the archived IBM Q2 experiment through the original #254 analyzer.

Read-only: no IBM service access or hardware submission.
Run from the recovered_q2 directory with its pinned requirements installed.
"""
from __future__ import annotations

import json
import math
from pathlib import Path
from hardware_analysis import summarize

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT.parent / "receipts" / "hardware_q2"
EXPECTED_JOB = "dc1vksqnj2vs73dfu0n0"


def read(name: str):
    return json.loads((ARCHIVE / name).read_text(encoding="utf-8"))


def replay() -> dict:
    manifest = read("manifest.json")
    protocol = read("q2_protocol.json")
    hardware = read("hardware_counts.json")
    expected = read("hardware_analysis.json")
    observed = summarize(manifest, protocol["scans"], hardware)
    if observed != expected:
        raise AssertionError("reconstructed analysis differs from the immutable IBM Q2 receipt")
    if observed["job_id"] != EXPECTED_JOB or observed["shots_total"] != 73_728:
        raise AssertionError("the IBM job identity or shot total changed")
    if not observed["primary_acceptance"]["passes"]:
        raise AssertionError("the prespecified primary criterion did not pass")
    if not observed["tree_rectangle_contains_origin"]:
        raise AssertionError("the tree control does not contain the origin")
    positive = observed["four_phase_groups"]["signal_t1.6"]["reference_calibrated_phase"]
    reversed_phase = observed["four_phase_groups"]["reversed_t1.6"]["reference_calibrated_phase"]
    fwd = math.degrees(positive["relative_phase_rad"])
    rev = math.degrees(reversed_phase["relative_phase_rad"])
    if abs(fwd - 38.90366216407) > 1e-7 or abs(rev + 42.85997335229) > 1e-7:
        raise AssertionError("the signed phase estimates diverge from Q2 counts")
    return {
        "status": "PASS_READ_ONLY",
        "source": "MathCan #254 archived IBM job, independently replayed on current main",
        "job_id": EXPECTED_JOB,
        "shots_total": observed["shots_total"],
        "forward_degrees": fwd,
        "reversed_degrees": rev,
        "primary_passes": True,
        "tree_contains_zero": True,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2))

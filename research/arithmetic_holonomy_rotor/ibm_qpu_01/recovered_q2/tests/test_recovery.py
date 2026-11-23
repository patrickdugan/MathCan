"""Safety gates and offline IBM job recovery for the historical #254 code."""
from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from experiment import Hold, collect, submission
from offline_replay import ARCHIVE, replay

ROOT = Path(__file__).resolve().parents[1]


def load(name: str):
    return json.loads((ARCHIVE / name).read_text(encoding="utf-8"))


def test_archived_hardware_analysis_replays_identically():
    receipt = replay()
    assert receipt["status"] == "PASS_READ_ONLY"
    assert receipt["shots_total"] == 73_728
    assert 38 < receipt["forward_degrees"] < 40
    assert -44 < receipt["reversed_degrees"] < -42


def test_legacy_submission_requires_independent_new_approval(tmp_path, monkeypatch):
    for var in (
        "AHR_QPU_ALLOW_LIVE_SUBMISSION",
        "AHR_QPU_FREE_PLAN_VERIFIED",
        "AHR_QPU_LEGACY_RECOVERY_APPROVED",
        "AHR_QPU_APPROVED_MANIFEST_SHA256",
    ):
        monkeypatch.delenv(var, raising=False)
    with pytest.raises(Hold, match="separate approval"):
        submission(None, tmp_path, 2048, authorized=False)
    with pytest.raises(Hold, match="three explicit YES guards"):
        submission(None, tmp_path, 2048, authorized=True)
    for var in (
        "AHR_QPU_ALLOW_LIVE_SUBMISSION",
        "AHR_QPU_FREE_PLAN_VERIFIED",
        "AHR_QPU_LEGACY_RECOVERY_APPROVED",
    ):
        monkeypatch.setenv(var, "YES")
    (tmp_path / "manifest.json").write_text('{"protocol":"test"}', encoding="utf-8")
    monkeypatch.setenv("AHR_QPU_APPROVED_MANIFEST_SHA256", "0" * 64)
    with pytest.raises(Hold, match="exact manifest SHA256"):
        submission(None, tmp_path, 2048, authorized=True)


def test_interrupted_hardware_collection_recovers_tag_offline(tmp_path):
    manifest = load("manifest.json")
    counts = load("hardware_counts.json")["counts"]
    protocol = load("q2_protocol.json")
    job_id = "dc1vksqnj2vs73dfu0n0"
    tag = "ahr-qpu-01-recovery-test"

    for filename, content in (
        ("manifest.json", manifest),
        ("q2_protocol.json", protocol),
        ("hardware_job.json", {
            "tag": tag,
            "job_id": None,
            "backend": "ibm_fez",
            "shots_per_circuit": 2048,
        }),
    ):
        (tmp_path / filename).write_text(json.dumps(content), encoding="utf-8")

    class CountRegister:
        def __init__(self, data):
            self.data = data
        def get_counts(self):
            return dict(self.data)

    ordered_pubs = [
        SimpleNamespace(data=SimpleNamespace(out=CountRegister(counts[case])))
        for case in manifest["case_order"]
    ]

    class FakeJob:
        def job_id(self):
            return job_id
        def status(self):
            return "DONE"
        def result(self):
            return ordered_pubs
        def usage(self):
            return 21

    job = FakeJob()

    class FakeService:
        def active_instance(self):
            return "open-test"
        def instances(self):
            return [{"crn": "open-test", "plan": "open", "pricing_type": "free"}]
        def usage(self):
            return {"usage_remaining_seconds": 515}
        def jobs(self, *, job_tags, instance, limit):
            assert job_tags == [tag] and instance == "open-test" and limit == 2
            return [job]
        def job(self, requested):
            assert requested == job_id
            return job

    result = collect(FakeService(), tmp_path)
    assert result["job_id"] == job_id
    assert result["status"] == "DONE"
    assert result["counts"] == counts
    assert result["primary_acceptance"]["passes"]
    assert json.loads((tmp_path / "hardware_job.json").read_text())["job_id"] == job_id
    assert json.loads((tmp_path / "hardware_counts.json").read_text())["counts"] == counts

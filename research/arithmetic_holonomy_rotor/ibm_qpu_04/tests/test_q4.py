"""Offline mathematical, statistical, and archived ISA checks."""
from hashlib import sha256
import json
from pathlib import Path
import sys

import numpy as np
from qiskit import qpy

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from circuits import verify_links, verify_paths
from endpoints import from_counts, model_endpoints, wilson
from model import A, B, LABELS, Y, Case, audit, cases, edge_link, oracle, rotation, walk


def test_involution_and_reverse_path():
    unitary = rotation("x", .41)
    link = edge_link(1, 3, unitary)
    np.testing.assert_allclose(link @ link, np.eye(16), atol=1e-14)
    np.testing.assert_allclose(link, link.conj().T, atol=1e-14)
    np.testing.assert_allclose(link, edge_link(3, 1, unitary.conj().T), atol=1e-14)
    primary = Case("primary", "signal", "AB")
    for path in (A, B):
        np.testing.assert_allclose(walk(primary, path[::-1]), walk(primary, path).conj().T, atol=1e-14)
    assert audit()["angle_pairs"] == 20


def test_full_space_synthesis_and_path_vertices():
    assert max(verify_links().values()) < 1e-12
    for variant in verify_paths().values():
        assert variant["AB"] == list(A[1:] + B[1:])
        assert variant["BA"] == list(B[1:] + A[1:])


def test_route_controls_and_balance():
    def internal(arm, label):
        return oracle(Case(f"{arm}/{label}", arm, label))[1]

    for arm in ("commuting", "identity", "inverse", "pure_gauge", "same_link"):
        a, b = [internal(arm, label) for label in LABELS]
        np.testing.assert_allclose(abs(np.vdot(a, b)), 1., atol=1e-14)
    reverse = [internal("reverse", label) for label in LABELS]
    np.testing.assert_allclose([np.vdot(s, Y @ s).real for s in reverse], [1, -1], atol=1e-14)
    for arm in ("inverse", "pure_gauge"):
        np.testing.assert_allclose(abs(internal(arm, "AB")), [1, 0], atol=1e-14)
    specification = cases()
    assert len({s.id for s in specification}) == len(specification) == 76
    assert sum(s.label == "AB" for s in specification if s.arm != "prepare") == 30


def test_joint_endpoint_includes_leakage():
    p = np.zeros(16)
    p[[0, 8, 9]] = [.10, .60, .30]
    answer = model_endpoints(p, "AB")
    np.testing.assert_allclose(answer["return"], .70)
    np.testing.assert_allclose(answer["joint_correct_and_return"], .60)
    np.testing.assert_allclose(answer["conditional_correct"], 6/7)
    sample = from_counts(p*1000, "AB")
    assert sample["shots"] == 1000 and sample["joint_successes"] == 600
    np.testing.assert_allclose([wilson(0, 100)[0], wilson(100, 100)[1]], [0, 1], atol=1e-14)


def test_archived_workload_and_scope():
    r = ROOT / "receipts"
    m = json.loads((r / "manifest.json").read_text(encoding="utf-8"))
    assert m["qpu_submitted"] is False and m["hardware_decision"] == "HOLD"
    assert m["circuit_count"] == 76 and m["shots"] == 155648
    cal = (r / "calibration.json").read_text(encoding="utf-8").encode()
    assert sha256(cal).hexdigest() == m["snapshot_sha256"]
    selected = next(s for s in json.loads(cal)["snapshots"]
                    if s["selection"]["physical_xyz"] == m["physical_qubits"])
    instructions = {(row["gate"], tuple(row["physical"])) for row in selected["instructions"]}
    file = r / "q4_candidate_isa.qpy"
    assert sha256(file.read_bytes()).hexdigest() == m["qpy_sha256"]
    with file.open("rb") as stream:
        circuits_ = qpy.load(stream)
    assert len(circuits_) == len(m["cases"])
    for circuit, row in zip(circuits_, m["cases"], strict=True):
        assert circuit.metadata["case_id"] == row["case"]["id"]
        measured = {}
        for op in circuit.data:
            name = op.operation.name
            physical = tuple(circuit.find_bit(q).index for q in op.qubits)
            assert (name, physical) in instructions or name in {"delay", "barrier"}
            assert set(physical) <= set(m["physical_qubits"])
            if name == "measure":
                measured[circuit.find_bit(op.clbits[0]).index] = physical[0]
        assert [measured[i] for i in range(4)] == row["measurement_by_classical_bit"]
    s = json.loads((r / "simulation.json").read_text(encoding="utf-8"))
    assert s["oracle"]["identity_compilation_audit"]["remaining_unitary_after"] == 0
    assert m["simulation_gate"] == (
        "PASS" if all(a["passes"] for a in s["scenarios"].values()) else "FAIL")
    for arm in s["scenarios"].values():
        assert len(arm["rows"]) == 76
        assert all(sum(row["counts"]) == 2048 for row in arm["rows"].values())

"""Verify the merged Q2 reference without modifying the byte archive."""
import importlib.util
from pathlib import Path

import numpy as np
from qiskit import qpy

BASE = "2efb49fe12b1dfc46434793042efc6daddda16e2"
SOURCE = Path(__file__).resolve().parent.parent / "ibm_qpu_01"


def q2_audit():
    spec = importlib.util.spec_from_file_location("upstream_q2", SOURCE / "hardware_q2_replay.py")
    upstream = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(upstream)
    report = upstream.validate()
    manifest = upstream.read("manifest.json")
    calibration = upstream.read("calibration.json")
    with (upstream.ROOT / "q2_isa.qpy").open("rb") as stream:
        circuits = qpy.load(stream)
    assert [c.metadata["case_id"] for c in circuits] == manifest["case_order"]
    allowed = {(r["gate"], tuple(r["physical"])) for r in calibration["instructions"]}
    for circuit in circuits:
        measured = {}
        for item in circuit.data:
            qubits = tuple(circuit.find_bit(q).index for q in item.qubits)
            assert (item.operation.name, qubits) in allowed
            if item.operation.name == "measure":
                measured[circuit.find_bit(item.clbits[0]).index] = qubits[0]
        assert [measured[0], measured[1]] == [9, 10]
    analysis = upstream.read("hardware_analysis.json")
    primary = analysis["primary_acceptance"]
    exact = upstream.read("q2_protocol.json")["scans"]["exact"]["signal_t1.6"]
    target = np.array([(exact[0] - exact[2])/2, (exact[3] - exact[1])/2])
    np.testing.assert_allclose(target, primary["target"], atol=1e-12)
    for bounds, value in zip(primary["expanded_joint_rectangle"], target):
        assert bounds[0] <= value <= bounds[1]
    for axis, (bounds, allowance) in enumerate(zip(
            [primary["unexpanded_joint_95_rectangle"][k] for k in ("real", "imag")],
            primary["systematic_allowances_real_imag"])):
        np.testing.assert_allclose([bounds[0] - allowance, bounds[1] + allowance],
                                   primary["expanded_joint_rectangle"][axis], atol=1e-12)
    tree = analysis["four_phase_groups"]["tree_t1.6"]["raw_joint_95_rectangle"]
    assert all(tree[axis][0] <= 0 <= tree[axis][1] for axis in ("real", "imag"))
    return {"mathcan_base": BASE, "merge_pr": 262, "original_draft_pr": 254,
            "status_pr": 264, "calibration_sha256": manifest["calibration_sha256"],
            "qpy_sha256": manifest["qpy_sha256"], "exact_primary": target.tolist(),
            "primary_acceptance_replayed": True, "qpy_layout_verified": True, **report}

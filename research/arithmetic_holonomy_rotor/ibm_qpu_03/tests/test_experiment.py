from copy import deepcopy
from dataclasses import replace
from datetime import datetime, timedelta, timezone
from hashlib import sha256
from pathlib import Path
import json
import runpy
import sys
from types import SimpleNamespace

import numpy as np
import pytest
from qiskit import qpy
from qiskit_aer.noise import NoiseModel, thermal_relaxation_error

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from backend_snapshot import calibration_fingerprint, historical_errors
from bianchi_reconstruction import project, reconstruct
from circuit_synthesis import compact_target, measure_map, physical_archive
from controls import CENTER, exact_controls
from fisher_design import (allocate, fisher, mirror_reference, nuisance_templates, response)
from noise_benchmark import CalibratedAer, benchmark, quantum_instruction
from plaquette_estimator import direct_probability, probability, settings, short_time_audit
from provenance import q2_audit
from q3_hamiltonian import (BIANCHI, CHORD_COLUMNS, D0, D1, EDGES, audit, chord_field,
                            face_flux, gauge_transform, matrix, phases_from_faces, wrap)


@pytest.fixture(scope="module")
def snapshot():
    return json.loads((ROOT / "receipts/calibration.json").read_text(encoding="utf-8"))["backend"]


def test_integer_chains_and_tree_gauge():
    assert audit()["d1_smith_diagonal"] == [1, 1, 1, 1, 1, 0]
    rng = np.random.default_rng(22)
    original = rng.uniform(-np.pi, np.pi, size=(30, 12))
    tree = [i for i in range(12) if i not in CHORD_COLUMNS]
    gauge = np.linalg.solve(D0[tree, 1:], original[:, tree].T).T
    transformed = gauge_transform(original, np.column_stack((np.zeros(len(gauge)), gauge)))
    np.testing.assert_allclose(transformed[:, tree], 0, atol=2e-14)
    recovered = phases_from_faces(face_flux(original))
    np.testing.assert_allclose(wrap(recovered - transformed[:, CHORD_COLUMNS]), 0, atol=2e-14)
    assert not np.any(BIANCHI @ D1)


def test_circulation_selector_and_independent_oracles():
    field = chord_field(CENTER)
    cases = settings([.57])
    assert len({s.id for s in cases}) == 24
    exact = probability(field, cases)
    np.testing.assert_allclose(exact, [direct_probability(field, s) for s in cases], atol=2e-14)
    oracle = runpy.run_path(str(ROOT.parent / "ibm_qpu_01/hamiltonian.py"))["hypercube_hamiltonian"]
    for c in cases:
        marked = field.copy()
        marked[c.edge] += c.direction*c.offset
        np.testing.assert_allclose(matrix(marked), oracle(3, dict(zip(EDGES, -marked))), atol=2e-14)
    report = short_time_audit(field, np.linspace(.8, 1.3, 12))
    assert len(report["selectors"]) == 6
    assert exact_controls(1.4)["tree_flux_spread"] < 2e-14


def test_full_likelihood_jacobian_and_fisher():
    cases = settings([1.35])
    p, j = response(np.stack([CENTER, -.8*CENTER]), cases)
    h = 1e-5
    for k in range(5):
        direction = np.eye(5)[k]*h
        for i, center in enumerate([CENTER, -.8*CENTER]):
            low, high = probability(chord_field(np.stack([center-direction, center+direction])), cases)
            np.testing.assert_allclose(j[i, :, k], (high-low)/(2*h), atol=4e-9)
    templates = nuisance_templates(CENTER, cases, p[0], .01)
    jac = np.column_stack((j[0], templates))
    shots = allocate(p[0], jac, 98304, 4)
    assert sum(shots) == 98304 and len(shots) == 24
    assert np.linalg.eigvalsh(fisher(p[0], jac, shots, 4))[0] > 0
    assert len(set(mirror_reference(cases))) < len(cases)


def test_bianchi_with_correlated_covariance_and_wrapped_residual():
    truth = face_flux(chord_field([np.pi-.03, -.14, .27, -.41, .17]))
    covariance = .05*np.eye(6) + .03*np.ones((6, 6))
    raw = wrap(truth + .06*covariance@BIANCHI)
    projected, refined, residual = project(raw, covariance)
    np.testing.assert_allclose(wrap(projected-truth), 0, atol=2e-14)
    np.testing.assert_allclose(refined @ BIANCHI, 0, atol=2e-14)
    assert abs(residual) > .01
    _, chord_cov = reconstruct(projected, refined)
    assert np.linalg.eigvalsh(chord_cov)[0] > 0


def test_native_layout_noisy_model_and_edge_formula(snapshot):
    target = compact_target(snapshot)
    aer = CalibratedAer(snapshot)
    cases = [replace(s, time=.3) for s in settings([.3])[2::4]]
    field = chord_field(CENTER)
    exact, circuits, native, noisy = benchmark(field, cases, "exact", target, snapshot, aer)
    assert exact["max_abs_probability_error"] < 1e-12
    assert np.all((noisy > 0) & (noisy < 1))
    assert max(abs(native-noisy)) > 1e-4
    assert exact["max_two_qubit_gates"] > 0 and exact["max_circuit_duration_s"] > 0
    physical = snapshot["selection"]["physical_xyz"]
    for c in circuits:
        assert measure_map(physical_archive(c, snapshot)) == [physical[q] for q in measure_map(c)]
    low, *_ = benchmark(field, cases[:2], "edge-2", target, snapshot, aer)
    high, *_ = benchmark(field, cases[:2], "edge-4", target, snapshot, aer)
    assert high["max_abs_probability_error"] < .4*low["max_abs_probability_error"]


def test_serialized_kraus_channel_roundtrip():
    model = NoiseModel()
    noise = thermal_relaxation_error(t1=1e-4, t2=1.5e-4, time=1e-6)
    model.add_quantum_error(noise, "sx", [0])
    encoded = model.to_dict(serializable=True)["errors"][0]["instructions"][0][0]
    original = noise.to_dict()["instructions"][0][0]
    assert encoded["name"] == "kraus"
    restored = quantum_instruction(encoded)
    np.testing.assert_allclose(restored["params"], original["params"], atol=1e-15)


def test_prior_calibration_is_strictly_earlier():
    current = datetime(2026, 11, 23, tzinfo=timezone.utc)
    parameter = SimpleNamespace(name="gate_error", value=.002)
    gate = SimpleNamespace(gate="cz", qubits=[9, 10], parameters=[parameter])
    latest = SimpleNamespace(last_update_date=current)
    prior = SimpleNamespace(last_update_date=current-timedelta(hours=1), gates=[gate])

    def properties(datetime):
        assert datetime < current
        return prior

    errors, record = historical_errors(SimpleNamespace(properties=properties), latest)
    assert errors == {("cz", 9, 10): .002}
    assert record["prior_timestamp"] == prior.last_update_date.isoformat()
    errors, record = historical_errors(SimpleNamespace(properties=lambda datetime: latest), latest)
    assert not errors and record["status"] == "no_distinct_prior_calibration"


def test_calibration_identity_and_model_fingerprints(snapshot):
    new = deepcopy(snapshot)
    new["calibration_timestamp"] = "2026-11-23T23:19:00+08:00"
    assert calibration_fingerprint(snapshot) != calibration_fingerprint(new)
    model = calibration_fingerprint(snapshot, include_calibration_identity=False)
    assert model == calibration_fingerprint(new, include_calibration_identity=False)
    new["instructions"][0]["duration_s"] = 1e-3
    assert model != calibration_fingerprint(new, include_calibration_identity=False)


def test_archive_q2_receipt():
    report = q2_audit()
    assert report["forward_deg"] > 0 > report["reverse_deg"]
    assert report["primary_acceptance_replayed"]


@pytest.mark.parametrize("archive", ["receipts", "receipts/live", "receipts/execution_refresh"])
def test_archive_q3_receipts(archive):
    receipt = ROOT / archive
    manifest = json.loads((receipt / "q3_candidate_manifest.json").read_text(encoding="utf-8"))
    qpy_file = receipt / "q3_candidate_isa.qpy"
    assert sha256(qpy_file.read_bytes()).hexdigest() == manifest["qpy_sha256"]
    cal = (receipt / "calibration.json").read_text(encoding="utf-8")
    assert sha256(cal.encode("utf-8")).hexdigest() == manifest["calibration_sha256"]
    snapshot = json.loads(cal)
    allowed = {(r["gate"], tuple(r["physical"])) for r in snapshot["backend"]["instructions"]}
    with qpy_file.open("rb") as stream:
        circuits = qpy.load(stream)
    assert len(circuits) == manifest["circuits"]
    for row, circuit in zip(manifest["settings"], circuits):
        assert row["case_id"] == circuit.metadata["case_id"]
        assert measure_map(circuit) == row["classical_bit_to_physical"]
        assert row["shots"] == 4096
        assert set(measure_map(circuit)) == set(manifest["physical_xyz"])
        for item in circuit.data:
            qubits = tuple(circuit.find_bit(q).index for q in item.qubits)
            assert (item.operation.name, qubits) in allowed
    assert sum(row["shots"] for row in manifest["settings"]) == manifest["total_shots"]
    assert not manifest["qpu_submitted"] and not manifest["approval_granted"]
    if archive == "receipts/live":
        recheck = json.loads((receipt / "calibration_recheck.json").read_text(encoding="utf-8"))
        assert recheck["same_compilation_and_noise_inputs"]
        assert (recheck["repeat_calibration_fingerprint"] ==
                calibration_fingerprint(snapshot["backend"]))
        assert recheck["repeat_account_check"]["plan"] == "open"
        assert recheck["initial_account_check"] == manifest["current_verified_open_plan"]
    elif archive == "receipts/execution_refresh":
        comparison = json.loads((receipt / "refresh_evidence.json").read_text(encoding="utf-8"))
        manifest_text = (receipt / "q3_candidate_manifest.json").read_text(encoding="utf-8")
        assert comparison["refreshed_manifest_sha256"] == sha256(manifest_text.encode()).hexdigest()
        previous = ROOT / "receipts/live"
        prior_text = (previous / "q3_candidate_manifest.json").read_text(encoding="utf-8")
        assert comparison["previous_manifest_sha256"] == sha256(prior_text.encode()).hexdigest()
        statistics = (previous / "statistics.json").read_text(encoding="utf-8")
        assert comparison["previous_statistics_sha256"] == sha256(statistics.encode()).hexdigest()
        assert comparison["previous_calibration_timestamp"] != manifest["calibration_timestamp"]
        assert comparison["refreshed_calibration_timestamp"] == manifest["calibration_timestamp"]
        assert comparison["simulation_inputs_sha256"] == calibration_fingerprint(
            snapshot["backend"], include_calibration_identity=False)
        assert comparison["case_order_shots_and_readout_maps_unchanged"]
        assert max(comparison["max_return_probability_changes"].values()) < 1e-12

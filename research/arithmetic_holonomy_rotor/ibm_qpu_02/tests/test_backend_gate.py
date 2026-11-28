"""AHR-QPU-02: pure tests and pinned mock-backend compilation smoke."""
from pathlib import Path
import sys
import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from backend_gate import read_only_inventory, bootstrap_phase, wrapped_error


def test_cloud_inventory_guard_without_connection():
    with pytest.raises(RuntimeError, match="--authorize-cloud"):
        read_only_inventory(None, False)


def test_bootstrap_phase_recovers_reference_angle():
    theta = .4
    phase_grid = np.arange(4) * np.pi / 2
    p0 = .5 + .2 * np.cos(phase_grid)
    p1 = .5 + .2 * np.cos(theta + phase_grid)
    draws = bootstrap_phase(p1, p0, shots=8192, reps=300, seed=77)
    assert np.mean(np.abs(draws - theta)) < .06
    assert np.all(np.isfinite(draws))


def test_wrapped_error_across_pi_boundary():
    assert abs(wrapped_error(2*np.pi-.01, 0) + .01) < 1e-12


def test_fake_compilation_and_noisy_simulator(tmp_path):
    pytest.importorskip("qiskit")
    pytest.importorskip("qiskit_ibm_runtime")
    pytest.importorskip("qiskit_aer")
    from backend_gate import local_mock_audit
    result = local_mock_audit(shots=256, theta=.73, t=1.6,
                              output=tmp_path / "report.json")
    assert result["status"] == "PASS"
    assert result["circuit_count"] == 12
    assert result["total_shots"] == 3072
    assert result["synthesis_comparison"][0]["max_ideal_p00_error"] < 1e-8
    assert np.isfinite(result["theta_estimate"])
    assert result["hardware_submission"] is False
    assert result["account_allocation_checked"] is False
    assert (tmp_path / "report.json").is_file()

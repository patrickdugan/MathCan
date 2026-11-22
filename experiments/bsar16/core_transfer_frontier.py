"""BSAR-16I: exact L2-to-vorticity-core obstruction and H4 transfer gate.

A smooth high-frequency divergence-free Fourier perturbation may have
arbitrarily small velocity L2 norm while moving the actual continuum
half-maximum vorticity core away from the BSAR-14 anchor pair.

For a separate positive result, a rational lattice-shell estimate shows
||curl e||_infinity < 3 ||e||_(inhomogeneous H4). Re-audit every BSAR-16C
exact Galerkin core certificate and give a uniform *conditional* H4
velocity-error threshold for transferring those anchors to any smooth
full-PDE velocity field. No full-PDE H4 error estimate is supplied here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from functools import lru_cache
from pathlib import Path
from typing import Any

from experiments.bsar16.core_intervals import generate as core_generate
from experiments.bsar16.exact_residual import (
    GRID_SIZES, ROOTS, Q, SOURCE_BSAR14_BLOB, SOURCE_MATHCAN, encode,
)
from scripts.bsar14_initial_triad_transfer import (
    exact_point, modes as exact_source_modes,
)

SOURCE_BSAR16C_ROWS_SHA256 = (
    "aabf443503a9f30b16f3a1e8701b1a187075091cdbc4c8e811e250ab06f925cb"
)
REGISTERED_H4_ERROR_UPPER = Q(1, 20)
CURL_EMBEDDING_UPPER = Q(3)
LATTICE_RADIUS = 8
M_VALUES = (1, 2, 4, 8, 16, 32)
MIN_GALERKIN_MARGIN = Q(3, 5)
MIN_GALERKIN_ANCHOR = Q(4)
MIN_GALERKIN_DIRECTION_GAP = Q(1)
MIN_FULL_CORE_MARGIN = Q(3, 20)
MIN_FULL_DIRECTION_GAP = Q(4, 5)


def c4_squared_upper(radius: int = LATTICE_RADIUS) -> Q:
    """Exact rational lattice upper bound for ||curl e||_inf / ||e||_H4.

    For rho=max_i |k_i| >=1, the shell contains 24*rho^2+2 lattice
    vectors, |k|^2<=3*rho^2, and (1+|k|^2)^4 >=(1+rho^2)^4.
    The rho>R tail is at most 24/R^3 + 6/(5R^5).
    """
    if radius < 1:
        raise ValueError("positive integer lattice radius required")
    body = sum(
        (
            Q(3*r*r*(24*r*r+2), (1+r*r)**4)
            for r in range(1, radius+1)
        ), Q(0)
    )
    tail = Q(24, radius**3)+Q(6, 5*radius**5)
    return body+tail


def exact_high_frequency_obstruction(n: int, phase: int, m: int) -> dict[str, Any]:
    """Exact obstruction to any L2-only full-core transfer.

    w_m=(0,(1/m)*cos(M x),0), M=24*N*m; hence
    ||w_m||_L2^2=1/(2m^2), curl(w_m)=-(M/m)*sin(Mx)*e_z.
    At x=0 and pi/N the curl vanishes, while at pi/(2M)
    its magnitude is exactly 24*N.
    """
    if (n, phase) not in ROOTS or m < 1:
        raise ValueError("registered positive source frequency/phase and m>=1")
    amplitude = Q(1, m)
    wave = 24*n*m
    assert wave % (2*n) == 0
    assert amplitude*wave == 24*n
    source = exact_source_modes(n, Q(1), phase)
    p0 = exact_point(source, n, x_pi_over_n=False)["vorticity"]
    p1 = exact_point(source, n, x_pi_over_n=True)["vorticity"]
    assert isinstance(p0, tuple) and isinstance(p1, tuple)
    assert tuple(x.real for x in p0) == (0, -n, -5*phase*n)
    assert tuple(x.real for x in p1) == (0, -n, 5*phase*n)
    assert all(x.imag == 0 for x in p0+p1)
    anchor_sq = sum((x.real*x.real for x in p0), Q(0))
    assert anchor_sq == 26*n*n
    assert anchor_sq < Q(36*n*n)

    # Exact source envelope ||curl(u0)|| <= sqrt(65)*N < 9*N.
    # Triangle inequality at x*=pi/(2*M) gives
    # max |curl(u0+w_m)| > 24*N - 9*N = 15*N.
    assert 65*n*n < 81*n*n
    peak_lower = 15*n
    assert peak_lower > 2*6*n
    return {
        "frequency_N": n,
        "phase_sigma": phase,
        "m": m,
        "additional_wave_M": wave,
        "perturbation_amplitude": encode(amplitude),
        "perturbation_velocity_L2_squared": encode(amplitude*amplitude/2),
        "divergence_free_mean_zero_real_smooth": True,
        "perturbation_curl_at_both_anchors_zero": True,
        "curl_at_quarter_wave_point_magnitude": encode(Q(24*n)),
        "new_global_curl_max_strictly_greater_than": encode(Q(peak_lower)),
        "original_anchor_curl_squared": encode(anchor_sq),
        "both_anchors_outside_new_true_half_core": True,
        "boundary": "smooth Fourier field perturbation, not an NSE trajectory",
    }


@lru_cache(maxsize=1)
def _read_galerkin_archive() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows, manifest = core_generate()
    if manifest["rows_sha256"] != SOURCE_BSAR16C_ROWS_SHA256:
        raise ValueError("BSAR-16C pinned rational core archive changed")
    if manifest["cases"] != 12 or manifest["certified_core_pairs"] != 12:
        raise ValueError("unexpected BSAR-16C core population")
    if manifest["source_bsar14_blob"] != SOURCE_BSAR14_BLOB:
        raise ValueError("BSAR-14 exact source blob changed")
    if manifest["source_exact_mathcan"] != SOURCE_MATHCAN:
        raise ValueError("BSAR-14 exact source commit changed")
    return rows, manifest


def transfer_certificate(source: dict[str, Any], h4_upper: Q) -> dict[str, Any]:
    """Check sufficient full-core margins from BSAR-16C Galerkin receipts.

    If ||u_true(t)-v_K(t)||_H4 <=1/20 over the entire interval,
    ||curl(u_true-v_K)||_inf < 3/20. The full PDE norm bound
    is a clearly stated unproved *hypothesis*.
    """
    if h4_upper < 0 or h4_upper > REGISTERED_H4_ERROR_UPPER:
        raise ValueError("positive H4 error allowance must be <=1/20")
    n, phase, grid = (
        source["frequency_N"], source["phase_sigma"], source["grid_M"]
    )
    if (n, phase) not in ROOTS or grid not in GRID_SIZES:
        raise ValueError("unexpected original source root or grid")
    g_epsilon = Q(source["max_vorticity_perturbation_upper"])
    permitted = Q(27, 100) if n == 1 else Q(61, 50)
    if not (0 <= g_epsilon < permitted):
        raise ArithmeticError("BSAR-16C source-dependent Galerkin drift too large")

    margin = Q(source["half_maximum_core_margin_lower"])
    anchor = Q(source["galerkin_anchor_vorticity_norm_lower"])
    direction = Q(source["normalized_direction_separation_lower"])
    if (not source["core_pair_certified"]
            or not source["positive_cone_witness_certified"]):
        raise ArithmeticError("source Galerkin anchor certificate invalid")
    if not (margin > MIN_GALERKIN_MARGIN
            and anchor > MIN_GALERKIN_ANCHOR
            and direction > MIN_GALERKIN_DIRECTION_GAP):
        raise ArithmeticError("registered rational Galerkin margins weakened")

    # Exact analytic C4<3. Use 3 as a conservative non-strict coefficient.
    eps = CURL_EMBEDDING_UPPER*h4_upper
    full_margin = margin-3*eps
    if not full_margin > MIN_FULL_CORE_MARGIN:
        raise ArithmeticError("full-core margin gate failed")
    if not anchor-eps > 0:
        raise ArithmeticError("full anchor could vanish")
    full_gap = direction-4*eps/(anchor-eps)
    if not full_gap > MIN_FULL_DIRECTION_GAP:
        raise ArithmeticError("full direction gap gate failed")
    witness = Q(7*n, 22)*full_gap*full_gap
    safe_witness = Q(56*n, 275)
    if not witness > safe_witness:
        raise ArithmeticError("full Fourier direction-cone lower witness failed")

    return {
        "frequency_N": n,
        "phase_sigma": phase,
        "grid_M": grid,
        "time_horizon": source["time_horizon"],
        "galerkin_curl_drift_upper": encode(g_epsilon),
        "galerkin_anchor_magnitude_lower": encode(anchor),
        "galerkin_half_core_margin_lower": encode(margin),
        "galerkin_direction_gap_lower": encode(direction),
        "conditional_full_velocity_H4_error_upper": encode(h4_upper),
        "full_curl_perturbation_upper": encode(eps),
        "conditional_full_half_core_margin_lower": encode(full_margin),
        "conditional_full_direction_gap_lower": encode(full_gap),
        "conditional_full_cone_lower": encode(witness),
        "simple_uniform_full_cone_lower": encode(safe_witness),
        "full_core_condition_met_if_H4_bound_proved": True,
        "full_PDE_H4_error_bound_proved": False,
        "analytic_scope": (
            "Sufficient threshold at all times when H4 closeness and smooth "
            "full PDE velocity hold; no actual NSE H4 error certificate"
        ),
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    square_bound = c4_squared_upper()
    if not (Q(0) < square_bound < Q(9)):
        raise ArithmeticError("integer-shell Fourier H4-to-curl bound failed")
    core_rows, source = _read_galerkin_archive()
    transfers = [
        transfer_certificate(row, REGISTERED_H4_ERROR_UPPER)
        for row in core_rows
    ]
    obstacles = [
        exact_high_frequency_obstruction(n, phase, m)
        for n, phase in ROOTS for m in M_VALUES
    ]
    rows = {"transfers": transfers, "l2_counterexamples": obstacles}
    canonical = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "experiment": "BSAR-16I exact L2-to-core obstruction and conditional H4 transfer",
        "source_bsar16c_rows_sha256": SOURCE_BSAR16C_ROWS_SHA256,
        "source_bsar14_blob": SOURCE_BSAR14_BLOB,
        "source_exact_mathcan": SOURCE_MATHCAN,
        "l2_obstruction_count": len(obstacles),
        "conditional_h4_core_cases": len(transfers),
        "lattice_radius": LATTICE_RADIUS,
        "lattice_fourier_curl_C4_squared_upper": encode(square_bound),
        "lattice_fourier_curl_C4_strict_upper": "3/1",
        "uniform_H4_velocity_error_threshold": encode(REGISTERED_H4_ERROR_UPPER),
        "uniform_core_margin_strict_lower": encode(MIN_FULL_CORE_MARGIN),
        "uniform_anchor_direction_gap_strict_lower": encode(MIN_FULL_DIRECTION_GAP),
        "uniform_cone_witness_strict_lower": "56N/275",
        "conditional_full_PDE_H4_error_proved": False,
        "independent_full_PDE_existence_through_T_proved": False,
        "boundary": (
            "Exact algebraic L2 obstruction; exact rational conditional H4 "
            "transfer; no full Navier-Stokes H4 error or lifespan proof"
        ),
        "rows_sha256": hashlib.sha256(canonical).hexdigest(),
    }
    return [rows], manifest


def freeze(out: Path) -> dict[str, Any]:
    records, manifest = generate()
    out.mkdir(parents=True, exist_ok=True)
    (out/"rows.json").write_bytes(
        json.dumps(records, sort_keys=True, separators=(",", ":")).encode()
    )
    (out/"manifest.json").write_text(
        json.dumps(manifest, sort_keys=True, indent=2)+"\n", encoding="utf-8"
    )
    return manifest


def audit(out: Path) -> dict[str, Any]:
    expected, manifest = generate()
    actual = json.loads((out/"rows.json").read_text(encoding="utf-8"))
    metadata = json.loads((out/"manifest.json").read_text(encoding="utf-8"))
    if actual != expected or metadata != manifest:
        raise ValueError("BSAR-16I Fourier core frontier archive changed")
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("generate", "audit"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = freeze(args.out) if args.action == "generate" else audit(args.out)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

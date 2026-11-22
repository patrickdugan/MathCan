"""BSAR-16E: continuous-time certified polygonal Fourier reconstruction.

Input: BSAR-16D's 16 full-node float64/rational certificate rows and SHA-256
manifest. For the real, Leray-projected numerical Fourier fields W_j, define
W_lin(t)=(1-theta)*W_j+theta*W_(j+1), theta=(t-t_j)/h.

A quadratic rational Taylor reference has an *exact interpolation remainder*
a2*theta*(1-theta)*h^2. Combine its rational coefficient norm with the
BSAR-16D node-to-reference certificates and BSAR-16B's Galerkin defect
majorant to bound the entire continuous polygonal path, spatially everywhere
and for all real t in [0,T].

This verifies a well-defined post-hoc reconstruction of the binary64 output.
It is NOT an RK4 dense-output formula, nor a validation of hidden FFT stages.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from experiments.bsar16.core_intervals import anchor_certificate_from_epsilon
from experiments.bsar16.exact_residual import GRID_SIZES, ROOTS, Q, encode
from experiments.bsar16.float64_snapshots import (
    COARSE_DT, FINE_DT, T_END, _galerkin_error_upper, verify_archive,
)
from experiments.bsar16.rational_enclosure import (
    ceil_sqrt, gradient_l1, norm_squared, taylor_data,
)

UNITS = "normalized torus Fourier L2; exact rational outward enclosures"
REGISTERED_PARENT_SHA256 = "9ef44ff668bb98e4c0d8ac925e13842ed10f3fa4230fd7ede2dd6740837c8e58"


def dense_run(node_run: dict[str, Any]) -> dict[str, Any]:
    """Certify the exact piecewise-linear real/Leray projection of RK4 nodes."""
    n = node_run["frequency_N"]
    phase = node_run["phase_sigma"]
    grid = node_run["grid_M"]
    dt = Q(node_run["dt_nominal_rational"])
    if (n, phase) not in ROOTS or grid not in GRID_SIZES:
        raise ValueError("unregistered initial root or Galerkin grid")
    if dt not in (COARSE_DT, FINE_DT) or (dt == FINE_DT and grid != 32):
        raise ValueError("unregistered time step")
    steps = T_END / dt
    if steps.denominator != 1 or node_run["steps"] != steps.numerator:
        raise ValueError("invalid registered time horizon")
    nodes = node_run["nodes"]
    if len(nodes) != steps.numerator+1:
        raise ValueError("missing numerical snapshot")
    for j, node in enumerate(nodes):
        if node["tick"] != j or Q(node["time"]) != j*dt:
            raise ValueError("corrupt rational node label")

    poly, defect, _ = taylor_data(n, phase, grid)
    g = [gradient_l1(x) for x in poly]
    d = [ceil_sqrt(norm_squared(x)) for x in defect]
    a2norm = ceil_sqrt(norm_squared(poly[2]))
    k = node_run["cutoff_K"]
    if k != (grid-1)//3:
        raise ValueError("inconsistent Galerkin cutoff")
    ck = ceil_sqrt(Q(k*(k+1)*(2*k+1)**3))

    # Exact quadratic interpolation remainder:
    # (1-theta)p(t_j)+theta p(t_{j+1})-p(t)
    #     = theta(1-theta) h^2 a2.
    remainder = dt**2 * a2norm/4
    intervals: list[dict[str, Any]] = []
    for j in range(steps.numerator):
        tleft = j*dt
        tright = (j+1)*dt
        left = Q(nodes[j]["raw_binary64_to_rational_reference_L2_upper"])
        right = Q(nodes[j+1]["raw_binary64_to_rational_reference_L2_upper"])
        if left < 0 or right < 0:
            raise ValueError("negative Fourier coordinate error")
        max_node_error = max(left,right)
        interpolation_to_p = max_node_error+remainder
        reference_to_v = _galerkin_error_upper(tright, d, g)
        polygon_to_v = interpolation_to_p+reference_to_v

        # Direct source-to-polygon pointwise curl control, valid at every t.
        source_drift = g[1]*tright+g[2]*tright*tright
        direct_epsilon = source_drift+ck*interpolation_to_p
        direct_core = anchor_certificate_from_epsilon(n, direct_epsilon)
        # Independent path via exact finite Galerkin ODE.
        via_epsilon = (
            source_drift+ck*reference_to_v+ck*polygon_to_v
        )
        via_core = anchor_certificate_from_epsilon(n, via_epsilon)
        intervals.append({
            "interval_index": j,
            "time_left": encode(tleft),
            "time_right": encode(tright),
            "quadratic_interpolation_remainder_L2_upper": encode(remainder),
            "polygon_to_rational_reference_L2_upper": encode(interpolation_to_p),
            "rational_reference_to_exact_galerkin_L2_upper": encode(reference_to_v),
            "polygon_to_exact_galerkin_L2_upper": encode(polygon_to_v),
            "polygon_continuum_core": direct_core,
            "polygon_continuum_core_via_galerkin": via_core,
        })

    return {
        "frequency_N": n,
        "phase_sigma": phase,
        "grid_M": grid,
        "cutoff_K": k,
        "dt_rational": encode(dt),
        "intervals": intervals,
        "original_float_state_sha256": node_run["float_state_sha256_le_complex128_C"],
        "quadratic_taylor_coefficient_L2_upper": encode(a2norm),
        "all_interval_direct_core_certified": all(
            x["polygon_continuum_core"]["positive_cone_witness_certified"]
            for x in intervals
        ),
        "all_interval_via_galerkin_core_certified": all(
            x["polygon_continuum_core_via_galerkin"][
                "positive_cone_witness_certified"
            ] for x in intervals
        ),
        "max_continuous_polygon_to_exact_galerkin_L2_upper": encode(
            max(Q(x["polygon_to_exact_galerkin_L2_upper"]) for x in intervals)
        ),
        "scope": (
            "All t in [0,T] for exact real/Leray-projected piecewise-linear "
            "reconstruction of stored binary64 Fourier nodes. No RK4 dense "
            "internal interpolant or full NSE pointwise core certification."
        ),
    }


def generate(source_dir: Path, *, expected_parent_sha256: str | None = None) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    parent = verify_archive(source_dir, rerun=False)
    if (expected_parent_sha256 is not None
            and parent["runs_sha256"] != expected_parent_sha256):
        raise ValueError("source BSAR-16D binary64 receipt digest changed")
    if parent["run_count"] != 16 or parent["snapshot_count"] != 256:
        raise ValueError("wrong BSAR-16D source campaign")
    node_runs = json.loads((source_dir/"runs.json").read_text(encoding="utf-8"))
    rows = [dense_run(x) for x in node_runs]
    data = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "experiment": "BSAR-16E continuous polygonal reconstruction of BSAR-16D RK4 nodes",
        "source_bsar16d_runs_sha256": parent["runs_sha256"],
        "time_horizon": encode(T_END),
        "run_count": len(rows),
        "interval_count": sum(len(x["intervals"]) for x in rows),
        "interval_direct_core_count": sum(
            int(interval["polygon_continuum_core"]["positive_cone_witness_certified"])
            for row in rows for interval in row["intervals"]
        ),
        "interval_via_galerkin_core_count": sum(
            int(interval["polygon_continuum_core_via_galerkin"]["positive_cone_witness_certified"])
            for row in rows for interval in row["intervals"]
        ),
        "rational_units": UNITS,
        "interpretation": "piecewise-linear projection of the exact binary64 Fourier node arrays",
        "explicit_exclusion": "not an internal RK4 dense extension or true NSE pointwise error",
        "rows_sha256": hashlib.sha256(data).hexdigest(),
    }
    return rows, manifest


def freeze(source: Path, out: Path, *, expected_parent_sha256: str | None = None) -> dict[str, Any]:
    rows, manifest = generate(source, expected_parent_sha256=expected_parent_sha256)
    out.mkdir(parents=True, exist_ok=True)
    (out/"rows.json").write_bytes(
        json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    )
    (out/"manifest.json").write_text(
        json.dumps(manifest, sort_keys=True, indent=2)+"\n", encoding="utf-8"
    )
    return manifest


def audit(source: Path, out: Path, *, expected_parent_sha256: str | None = None) -> dict[str, Any]:
    rows, manifest = generate(source, expected_parent_sha256=expected_parent_sha256)
    actual_rows = json.loads((out/"rows.json").read_text(encoding="utf-8"))
    actual_manifest = json.loads((out/"manifest.json").read_text(encoding="utf-8"))
    if rows != actual_rows or manifest != actual_manifest:
        raise ValueError("BSAR-16E polygonal rational certificate changed")
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("generate", "audit"))
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--expected-parent-sha256", default=None)
    args = parser.parse_args()
    report = (freeze(args.source, args.out, expected_parent_sha256=args.expected_parent_sha256)
              if args.action == "generate" else
              audit(args.source, args.out, expected_parent_sha256=args.expected_parent_sha256))
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

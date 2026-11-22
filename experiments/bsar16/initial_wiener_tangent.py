"""BSAR-16J-A: exact initial Fourier-Wiener and H4 Galerkin defect.

For the exact BSAR-14 initial polynomial, compare the full NSE velocity
tangent with the finite Galerkin ODE tangent. Their difference is exactly
-r_K(0), the omitted projected quadratic advection. Verify the L2, weighted
Fourier A1, curl L2 and inhomogeneous H4 norms using Gaussian rationals.

These are exact time-zero derivative values, NOT positive-time NSE error
estimates, a classical lifespan certificate, or a pointwise PDE core bound.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
from typing import Any

from experiments.bsar16.exact_residual import (
    GRID_SIZES, ROOTS, SOURCE_BSAR14_BLOB, SOURCE_MATHCAN, SOURCE_BSAR,
    Q, cutoff, encode, exact_decomposition, ksq, source_modes, squared_norm,
)

SOURCE_BSAR16A_MERGE = "ee55923801e5d85b90e6be654929d1a1fcfd3d5a"
NONZERO_HIGH_K = ((-2, -8, 0), (2, 8, 0))


def exact_sqrt(q: Q) -> Q:
    """Return exact rational square root or reject the unsupported case."""
    if q < 0:
        raise ValueError("negative rational cannot have real square root")
    top, bot = isqrt(q.numerator), isqrt(q.denominator)
    if top*top != q.numerator or bot*bot != q.denominator:
        raise ArithmeticError("not an exactly rational Fourier-mode magnitude")
    return Q(top, bot)


def source_tangent(n: int, phase: int, grid: int) -> dict[str, Any]:
    if (n, phase) not in ROOTS or grid not in GRID_SIZES:
        raise ValueError("unregistered exact source/grid")
    kmax = cutoff(grid)
    initial = source_modes(n, phase)
    result = exact_decomposition(initial, kmax)
    residual = result["high_residual"]
    l2sq = result["high_residual_l2_squared"]
    independent_l2sq = sum((squared_norm(v) for v in residual.values()), Q(0))
    assert l2sq == independent_l2sq

    a1 = sum(
        (exact_sqrt(Q(ksq(k))*squared_norm(v))
         for k, v in residual.items()), Q(0)
    )
    curl_l2sq = sum(
        (Q(ksq(k))*squared_norm(v) for k, v in residual.items()), Q(0)
    )
    h4sq = sum(
        (Q((1+ksq(k))**4)*squared_norm(v)
         for k, v in residual.items()), Q(0)
    )
    is_nonzero = n == 2 and grid in (16, 24)
    if is_nonzero:
        assert set(residual) == set(NONZERO_HIGH_K)
        assert l2sq == Q(1, 34)
        assert a1 == Q(2)
        assert curl_l2sq == Q(2)
        assert h4sq == Q(69**4, 34)
        for k in NONZERO_HIGH_K:
            assert ksq(k) == 68
            assert squared_norm(residual[k]) == Q(1, 68)
    else:
        assert not residual
        assert l2sq == a1 == curl_l2sq == h4sq == 0

    return {
        "frequency_N": n,
        "phase_sigma": phase,
        "grid_M": grid,
        "retained_cube_cutoff_K": kmax,
        "nonzero_initial_high_defect": is_nonzero,
        "high_mode_wavevectors": [list(k) for k in sorted(residual)],
        "full_minus_galerkin_velocity_tangent": "-high-mode projected convection",
        "source_high_mode_L2_squared": encode(l2sq),
        "source_high_mode_A1_wiener_norm": encode(a1),
        "source_high_mode_curl_L2_squared": encode(curl_l2sq),
        "source_high_mode_velocity_H4_squared": encode(h4sq),
        "fourier_A1_convention": "sum_{k} |k| |v_hat(k)|",
        "velocity_H4_convention": "sum_{k} (1+|k|^2)^4 |v_hat(k)|^2",
        "time_scope": "exact t=0 tangent only for local smooth full NSE",
        "future_full_PDE_curl_bound_proved": False,
        "future_full_PDE_H4_bound_proved": False,
        "full_PDE_smooth_through_T_proved": False,
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = [source_tangent(n, phase, grid)
            for n, phase in ROOTS for grid in GRID_SIZES]
    data = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "experiment": "BSAR-16J-A exact time-zero Fourier-Wiener Galerkin defect",
        "rows": len(rows),
        "nonzero_high_mode_cases": sum(x["nonzero_initial_high_defect"] for x in rows),
        "source_bsar16a_merge": SOURCE_BSAR16A_MERGE,
        "source_bsar14_blob": SOURCE_BSAR14_BLOB,
        "source_exact_mathcan": SOURCE_MATHCAN,
        "source_bsa_r": SOURCE_BSAR,
        "actual_full_NSE_local_smoothness": "known for smooth initial datum over some positive interval",
        "time_scope": "exact t=0 only; no enclosure at 0.012",
        "future_wiener_curl_residual_bound": "open",
        "future_quantitative_strong_lifespan": "open",
        "rows_sha256": hashlib.sha256(data).hexdigest(),
    }
    return rows, manifest


def freeze(out: Path) -> dict[str, Any]:
    rows, manifest = generate()
    out.mkdir(parents=True, exist_ok=True)
    (out/"rows.json").write_bytes(
        json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    )
    (out/"manifest.json").write_text(
        json.dumps(manifest, sort_keys=True, indent=2)+"\n", encoding="utf-8"
    )
    return manifest


def audit(out: Path) -> dict[str, Any]:
    rows, manifest = generate()
    actual_bytes = (out/"rows.json").read_bytes()
    if hashlib.sha256(actual_bytes).hexdigest() != manifest["rows_sha256"]:
        raise ValueError("BSAR-16J-A archive SHA-256 differs")
    observed = json.loads(actual_bytes)
    metadata = json.loads((out/"manifest.json").read_text(encoding="utf-8"))
    if observed != rows or metadata != manifest:
        raise ValueError("BSAR-16J-A exact initial-defect evidence differs")
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("generate", "audit"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = freeze(args.out) if args.action == "generate" else audit(args.out)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

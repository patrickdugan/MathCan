"""BSAR-16C: interval-certified Galerkin vorticity-core anchor pairs.

All reported bounds are rational and outward/inward rounded as appropriate.
The exact BSAR-14 anchor data and BSAR-16B validated continuous Galerkin
trajectory error yield a uniform sup-vorticity perturbation bound on [0,T].

Certificates refer to the *exact finite Galerkin ODE*. They do not certify
the floating-point RK4 trajectory or transfer pointwise vorticity/core
information to a full infinite-dimensional NSE solution.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
from typing import Any

from experiments.bsar16.exact_residual import (
    GRID_SIZES,
    ROOTS,
    SOURCE_BSAR,
    SOURCE_BSAR14_BLOB,
    SOURCE_MATHCAN,
    Q,
    encode,
)
from experiments.bsar16.rational_enclosure import (
    ROUNDING_SCALE,
    TIME_END,
    ceil_sqrt,
    enclosure,
    gradient_l1,
    round_up,
    taylor_data,
)

PI_UPPER = Q(22, 7)


def floor_sqrt(q: Q, scale: int = ROUNDING_SCALE) -> Q:
    """Exact rational lower bound for a nonnegative square root."""
    if q < 0 or scale <= 0:
        raise ValueError("expected nonnegative rational and positive scale")
    if q == 0:
        return Q(0)
    n = (q.numerator*scale*scale)//q.denominator
    lower = Q(isqrt(n), scale)
    assert lower*lower <= q
    return lower


def round_down(q: Q, scale: int = ROUNDING_SCALE) -> Q:
    if q < 0 or scale <= 0:
        raise ValueError("expected nonnegative rational and positive scale")
    return Q((q.numerator*scale)//q.denominator, scale)


def anchor_certificate_from_epsilon(n: int, epsilon: Q) -> dict[str, Any]:
    """Certified all-time Galerkin core witness given ||curl(v-v0)||_infty<=eps.

    Original anchor vorticities are (0,-N,-5*sigma*N) and
    (0,-N,+5*sigma*N). Their squared norm is 26*N^2 and their
    normalized direction difference squared is 50/13. The exact initial
    continuum vorticity maximum is bounded above by sqrt(65)*N.
    """
    if n <= 0 or epsilon < 0:
        raise ValueError("positive frequency and nonnegative epsilon required")
    anchor_start_lower = n*floor_sqrt(Q(26))
    global_start_upper = n*ceil_sqrt(Q(65))
    anchor_lower = anchor_start_lower-epsilon
    global_upper = global_start_upper+epsilon
    margin = 2*anchor_lower-global_upper
    core = anchor_lower > 0 and margin > 0

    direction_gap = Q(0)
    cone_K_lower = Q(0)
    if core:
        # For any nonzero vectors x,y:
        # |x/|x|-y/|y|| <= 2|x-y|/min(|x|,|y|).
        # Both anchor vectors remain at least anchor_lower in norm.
        direction_gap = (
            floor_sqrt(Q(50, 13))-4*epsilon/anchor_lower
        )
        if direction_gap > 0:
            # Torus geodesic distance between anchors is exactly pi/N.
            # pi < 22/7 implies N/pi > 7N/22.
            cone_K_lower = Q(7*n, 22)*direction_gap**2

    certified = core and direction_gap > 0 and cone_K_lower > 0
    return {
        "core_pair_certified": core,
        "positive_cone_witness_certified": certified,
        "max_vorticity_perturbation_upper": encode(round_up(epsilon)),
        "galerkin_global_vorticity_sup_upper": encode(round_up(global_upper)),
        "galerkin_anchor_vorticity_norm_lower": (
            encode(round_down(anchor_lower)) if anchor_lower > 0 else None
        ),
        "half_maximum_core_margin_lower": (
            encode(round_down(margin)) if margin > 0 else None
        ),
        "normalized_direction_separation_lower": (
            encode(round_down(direction_gap)) if direction_gap > 0 and core else None
        ),
        "cone_Kxi_anchor_lower": (
            encode(round_down(cone_K_lower)) if certified else None
        ),
        "rounding": "Gaussian rationals plus 1e-9 directed rational square-root rounding",
        "scope": (
            "Exact continuous Galerkin 3D vorticity core across [0,T]; "
            "not a float RK4 or infinite-dimensional NSE core certificate"
        ),
    }


def certify(n: int, phase: int, grid: int) -> dict[str, Any]:
    # First build the source-pinned rational Taylor solution and its
    # rigorous time-uniform Galerkin-vs-reference L2 error.
    polynomial, _, _ = taylor_data(n, phase, grid)
    g0 = gradient_l1(polynomial[0])
    assert g0 == 9*n, "the BSAR-14 source gradient Fourier bound changed"
    reference = enclosure(n, phase, grid)
    assert Q(reference["time_horizon"]) == TIME_END

    # BSAR-16B's gradient estimate is G0 + G1*T + G2*T^2
    # + C_K * ||v-p||_2, rounded UP to the 1e-9 rational grid.
    # As G0=9*N exactly, subtracting it gives an upper bound on
    # ||curl(v(t)-v(0))||_infty for every t in the registered interval.
    gradient_upper = Q(reference["validated_time_uniform_gradient_Linfty_upper"])
    epsilon = gradient_upper-g0
    assert epsilon >= 0
    witness = anchor_certificate_from_epsilon(n, epsilon)
    return {
        "frequency_N": n,
        "phase_sigma": phase,
        "grid_M": grid,
        "retained_cube_cutoff_K": reference["retained_cube_cutoff_K"],
        "time_horizon": encode(TIME_END),
        "source_anchor_points": ["(0,0,pi/(2N))", "(pi/N,0,pi/(2N))"],
        "initial_anchor_vorticity_squared": encode(Q(26*n*n)),
        "initial_global_vorticity_squared_upper": encode(Q(65*n*n)),
        "initial_normalized_direction_difference_squared": "50/13",
        "source_gradient_fourier_l1": encode(g0),
        "rational_reference_gradient_sup_upper": reference[
            "validated_time_uniform_gradient_Linfty_upper"
        ],
        "rational_reference_galerkin_L2_error_upper": reference[
            "validated_galerkin_L2_error_upper"
        ],
        **witness,
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = [certify(n, phase, grid) for n, phase in ROOTS for grid in GRID_SIZES]
    canonical = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    return rows, {
        "experiment": "BSAR-16C exact Galerkin interval vorticity core anchor",
        "cases": len(rows),
        "certified_core_pairs": sum(r["core_pair_certified"] for r in rows),
        "positive_cone_witnesses": sum(
            r["positive_cone_witness_certified"] for r in rows
        ),
        "source_exact_mathcan": SOURCE_MATHCAN,
        "source_bsar14_blob": SOURCE_BSAR14_BLOB,
        "source_bsa_r": SOURCE_BSAR,
        "time_horizon": encode(TIME_END),
        "vorticity_scope": "exact finite Galerkin ODE only",
        "not_validated": "BSAR-15 float RK4 and full NSE core transfer",
        "rows_sha256": hashlib.sha256(canonical).hexdigest(),
    }


def freeze(out: Path) -> dict[str, Any]:
    rows, manifest = generate()
    out.mkdir(parents=True, exist_ok=True)
    data = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    (out/"rows.json").write_bytes(data)
    (out/"manifest.json").write_text(
        json.dumps(manifest, sort_keys=True, indent=2)+"\n", encoding="utf-8"
    )
    return manifest


def audit(out: Path) -> dict[str, Any]:
    expected, manifest = generate()
    actual_rows = json.loads((out/"rows.json").read_text(encoding="utf-8"))
    actual_manifest = json.loads((out/"manifest.json").read_text(encoding="utf-8"))
    if expected != actual_rows or manifest != actual_manifest:
        raise ValueError("BSAR-16C rational core archive changed")
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

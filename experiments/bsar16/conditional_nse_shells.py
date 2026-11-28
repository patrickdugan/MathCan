"""BSAR-16G: conditional full-NSE low-shell transfer sign certificates.

A finite Fourier shell transfer is an L2-continuous trilinear observable
on divergence-free periodic velocities after integration by parts.
This transfers BSAR-16F's exact rational shell-polynomial sign margins to
the *full infinite-dimensional NSE solution*, conditional on a smooth
solution existing on the registered interval, using BSAR-16B's rational
PDE-to-Galerkin residual/error bound.

This says nothing about full-PDE pointwise vorticity-core membership,
a frequency-uniform lifespan, or global smooth Navier--Stokes regularity.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from experiments.bsar16.exact_residual import (
    GRID_SIZES,
    ROOTS,
    SOURCE_BSAR,
    SOURCE_BSAR14_BLOB,
    SOURCE_MATHCAN,
    Q,
    VISCOSITY,
    encode,
)
from experiments.bsar16.rational_enclosure import (
    TIME_END,
    ceil_sqrt,
    enclosure as rational_pde_enclosure,
    round_up,
)
from experiments.bsar16.shell_signs import (
    SHELLS,
    _basis,
    rational_error_at,
    reference_sign_margin,
    shell_gradient_l1,
    shell_modes,
    shell_trilinear_error,
)

DISPLAY_SCALE = 10**12


def round_down(q: Q, scale: int = DISPLAY_SCALE) -> Q:
    """Greatest rational multiple of 1/scale no larger than q."""
    if scale <= 0:
        raise ValueError("positive rational rounding scale required")
    return Q((q.numerator*scale)//q.denominator, scale)


def _conditional_gap(
    basis: dict[str, Any],
    n: int,
    phase: int,
    grid: int,
    shell: int,
    horizon: Q,
    source_pde: dict[str, Any],
) -> tuple[Q, Q, Q, Q, Q, Q]:
    """All inequalities hold for every t<=horizon, if smooth NSE exists."""
    if (n, phase) not in ROOTS or grid not in GRID_SIZES:
        raise ValueError("unregistered BSAR-14 source")
    if shell not in SHELLS or horizon <= 0 or horizon > TIME_END:
        raise ValueError("unregistered shell or time horizon")
    if Q(source_pde["time_horizon"]) != horizon:
        raise ValueError("mismatched PDE-to-Galerkin error horizon")
    if source_pde["frequency_N"] != n or source_pde["phase_sigma"] != phase:
        raise ValueError("mismatched source root")
    if source_pde["grid_M"] != grid:
        raise ValueError("mismatched source cutoff")
    if source_pde["viscosity"] != encode(VISCOSITY):
        raise ValueError("mismatched viscosity")

    # BSAR-16B proves, conditional on smooth NSE existence:
    # ||u_true(t)-v_K(t)||_2 <= Z_T for all 0<=t<=T.
    # The outward-1e-9 decimal stored in the B record is an upper bound.
    z = Q(source_pde["conditional_true_NSE_L2_error_upper_at_T"])
    if z < 0:
        raise ValueError("negative PDE-to-Galerkin L2 error")
    y = rational_error_at(horizon, basis["g"], basis["d"], basis["exp_n"])
    total = y + z

    # The source polynomial p is finite and solenoidal, while u_true-p may
    # have arbitrarily high Fourier modes. This is fine: the derivative in
    # the transfer is moved onto the FINITE shell Q_s by integration by parts.
    pnorm = sum(
        (basis["p"][j]*horizon**j for j in range(3)), Q(0)
    )
    shell_gradient = sum(
        (shell_gradient_l1(basis["polynomial"][j], n, shell)*horizon**j
         for j in range(3)), Q(0)
    )
    count = len(shell_modes(n, basis["cutoff"], shell))
    shell_constant = ceil_sqrt(Q(shell*n*n*count))
    reference_margin = reference_sign_margin(
        basis["transfers"][shell], horizon
    )
    conditional_error = shell_trilinear_error(
        total, pnorm, shell_gradient, shell_constant
    )
    return (
        reference_margin-conditional_error,
        reference_margin,
        conditional_error,
        total,
        y,
        z,
    )


def certify_shell(
    basis: dict[str, Any],
    n: int, phase: int, grid: int, shell: int,
    source_pde: dict[str, Any],
) -> dict[str, Any]:
    duration = TIME_END
    margin, reference, error, total, y, z = _conditional_gap(
        basis, n, phase, grid, shell, duration, source_pde
    )
    if margin <= 0:
        # A shorter interval is certified only under the same local smooth
        # existence premise on that shorter interval. Recompute *both*
        # the finite Galerkin and the full-PDE residual bound at its endpoint.
        found = False
        for subdivisions in range(1, 21):
            duration = TIME_END/(2**subdivisions)
            local_source = rational_pde_enclosure(
                n, phase, grid, horizon=duration
            )
            margin, reference, error, total, y, z = _conditional_gap(
                basis, n, phase, grid, shell, duration, local_source
            )
            if margin > 0:
                found = True
                break
        if not found:
            raise ArithmeticError("no certified rational conditional-PDE sign interval")

    signed_initial = basis["transfers"][shell][0]
    if signed_initial == 0 or margin <= 0:
        raise ArithmeticError("no strict conditional sign separation")
    return {
        "shell_normalized": shell,
        "original_signed_transfer": encode(signed_initial),
        "conditional_smooth_nse_existence_required": True,
        "certified_duration_if_smooth": encode(duration),
        "full_T_conditional_sign_certified": duration == TIME_END,
        "reference_signed_transfer_lower": encode(round_down(reference)),
        "full_NSE_to_galerkin_L2_upper": encode(round_up(z, DISPLAY_SCALE)),
        "galerkin_to_rational_reference_L2_upper": encode(round_up(y, DISPLAY_SCALE)),
        "full_NSE_to_rational_reference_L2_upper": encode(
            round_up(total, DISPLAY_SCALE)
        ),
        "finite_shell_transfer_error_upper": encode(round_up(error, DISPLAY_SCALE)),
        "conditional_full_NSE_signed_transfer_lower": encode(
            round_down(margin)
        ),
        "scope": (
            "Finite-shell T_s(u_true) sign, conditional on a smooth 3D periodic "
            "NSE solution on the stated interval. No pointwise NSE core proof."
        ),
    }


def certify(n: int, phase: int, grid: int) -> dict[str, Any]:
    basis = _basis(n, phase, grid)
    source = rational_pde_enclosure(n, phase, grid, horizon=TIME_END)
    if basis["transfers"][1][0] != Q(phase*n, 4):
        raise ArithmeticError("BSAR-14 source transfer identity altered")
    shells = [
        certify_shell(basis, n, phase, grid, s, source)
        for s in SHELLS
    ]
    return {
        "frequency_N": n,
        "phase_sigma": phase,
        "grid_M": grid,
        "retained_cutoff_K": basis["cutoff"],
        "viscosity": encode(VISCOSITY),
        "time_horizon": encode(TIME_END),
        "all_three_shells_conditional_full_T": all(
            x["full_T_conditional_sign_certified"] for x in shells
        ),
        "shells": shells,
        "PDE_hypothesis": (
            "The given BSAR-14 datum has a smooth incompressible periodic "
            "Navier-Stokes solution throughout the certified interval."
        ),
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = [certify(n, phase, grid) for n, phase in ROOTS for grid in GRID_SIZES]
    data = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "experiment": "BSAR-16G conditional full NSE finite-shell transfer signs",
        "case_count": len(rows),
        "conditional_shell_certificates": sum(len(x["shells"]) for x in rows),
        "cases_full_T_conditionally_certified": sum(
            x["all_three_shells_conditional_full_T"] for x in rows
        ),
        "source_exact_mathcan": SOURCE_MATHCAN,
        "source_bsar14_blob": SOURCE_BSAR14_BLOB,
        "source_bsa_r": SOURCE_BSAR,
        "viscosity": encode(VISCOSITY),
        "registered_horizon": encode(TIME_END),
        "condition": "smooth full 3D periodic NSE existence through the stated horizon",
        "shell_continuity": "periodic trilinear integration by parts; finite Q_s gradient",
        "explicit_exclusion": "no unconditional lifespan or pointwise full-NSE vorticity core",
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
        json.dumps(manifest, sort_keys=True, indent=2)+"\n",
        encoding="utf-8"
    )
    return manifest


def audit(out: Path) -> dict[str, Any]:
    expected_rows, expected_manifest = generate()
    actual_rows = json.loads((out/"rows.json").read_text(encoding="utf-8"))
    actual_manifest = json.loads((out/"manifest.json").read_text(encoding="utf-8"))
    if expected_rows != actual_rows or expected_manifest != actual_manifest:
        raise ValueError("BSAR-16G conditional full NSE sign certificate changed")
    return expected_manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("generate", "audit"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(
        freeze(args.out) if args.action == "generate" else audit(args.out),
        sort_keys=True, indent=2
    ))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

"""BSAR-16D: a posteriori, roundoff-inclusive error bounds for RK4 snapshots.

For each original BSAR-15 NumPy FFT/RK4 output, interpret its complex128
coefficients as exact binary rationals. A rational, upward-rounded L2 norm
bounds their difference from BSAR-16B's exact Gaussian-rational Taylor
reference at the *nominal rational time*. Combining with BSAR-16B's analytic
Gronwall bound certifies the snapshot's error relative to the exact finite
Galerkin ODE, without relying on an FFT internal error model.

The procedure certifies all *stored time nodes*, not a continuously
interpolated RK4 trajectory or a local RK4 defect. The real, solenoidal
interpreted field is the exact reality-symmetrized and Leray-projected
polynomial associated with each binary64 coefficient array. Orthogonal
projection cannot increase the L2 error from the real Galerkin reference.
It is not a certificate for the displayed FFT physical-grid numbers,
whose inverse-transform rounding would need a separate bound.

This is a finite-Galerkin certificate. Any full NSE error is conditional on
smooth PDE existence; pointwise NSE vorticity transfer remains open.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import sys
from fractions import Fraction
from math import isqrt
from pathlib import Path
from typing import Any

import numpy as np

from experiments.bsar15.galerkin import FourierGalerkin
from experiments.bsar16.core_intervals import anchor_certificate_from_epsilon
from experiments.bsar16.exact_residual import (
    GRID_SIZES, ROOTS, Q, VISCOSITY, Gaussian, Field, encode, zero_vec,
)
from experiments.bsar16.rational_enclosure import (
    ceil_sqrt, exp_upper, gradient_l1, norm_squared, polynomial_at,
    taylor_data,
)

T_END = Q(3, 250)
COARSE_DT = Q(1, 1000)
FINE_DT = Q(1, 2000)
COORDINATE_SCALE = 10**15
L2_NORM_SCALE = 10**15


def _ceil_abs_float_minus_fraction(x: float, target: Q, scale: int) -> int:
    """Bound |x-target| upward by an integer multiple of 1/scale exactly."""
    if not math.isfinite(x):
        raise ValueError("nonfinite binary64 Fourier coefficient")
    numerator, denominator = x.as_integer_ratio()
    combined = abs(numerator*target.denominator - target.numerator*denominator)
    divisor = denominator*target.denominator
    return (combined*scale + divisor-1)//divisor


def snapshot_reference_distance_upper(
    solver: FourierGalerkin, hats: np.ndarray, reference: Field,
    coordinate_scale: int = COORDINATE_SCALE,
    norm_scale: int = L2_NORM_SCALE,
) -> Q:
    """Directed-rational upper ||h_float - p||_2 over the *full* retained cube.

    Every binary64 coordinate is converted using its exact as_integer_ratio;
    every absolute scalar discrepancy is rounded UP onto the integer grid.
    Thus sqrt(sum of these squares) bounds the exact complex Hilbert norm.
    Neither np.linalg.norm nor an FFT is used in this error calculation.
    """
    if coordinate_scale <= 0 or norm_scale <= 0:
        raise ValueError("positive rational rounding scales required")
    if hats.shape != solver.initial.shape or hats.dtype != np.complex128:
        raise ValueError("expected the original 3 x M^3 complex128 array")
    if not bool(np.all(np.isfinite(hats))):
        raise ValueError("nonfinite numerical Fourier array")
    if bool(np.any(hats[:, ~solver.mask] != 0)):
        raise ValueError("unretained modes in numerical output")
    if bool(np.any(hats[:, 0, 0, 0] != 0)):
        raise ValueError("nonzero mean in numerical output")
    kmax = solver.cutoff
    for k, v in reference.items():
        if max(abs(j) for j in k) > kmax or k == (0, 0, 0):
            raise ValueError("reference has out-of-cube or mean mode")

    # Convert the entire retained array, including FFT roundoff-only modes.
    # Using an exact integer accumulation avoids a floating summation error.
    square_sum = 0
    empty = zero_vec()
    for kx in range(-kmax, kmax+1):
        ix = kx % solver.grid
        for ky in range(-kmax, kmax+1):
            iy = ky % solver.grid
            for kz in range(-kmax, kmax+1):
                iz = kz % solver.grid
                target = reference.get((kx, ky, kz), empty)
                for component in range(3):
                    actual = hats[component, ix, iy, iz]
                    ideal: Gaussian = target[component]
                    re = _ceil_abs_float_minus_fraction(
                        float(actual.real), ideal.real, coordinate_scale
                    )
                    im = _ceil_abs_float_minus_fraction(
                        float(actual.imag), ideal.imag, coordinate_scale
                    )
                    square_sum += re*re + im*im

    if square_sum == 0:
        return Q(0)
    # Compute ceil(norm_scale * sqrt(square_sum) / coordinate_scale)
    # using only integer floor-sqrt with a final outward increment.
    numerator = square_sum*norm_scale*norm_scale
    denominator = coordinate_scale*coordinate_scale
    scaled_squared_ceil = (numerator + denominator-1)//denominator
    root = isqrt(scaled_squared_ceil)
    if root*root < scaled_squared_ceil:
        root += 1
    return Q(root, norm_scale)


def _galerkin_error_upper(
    t: Q, defect_upper: list[Q], gradient_upper: list[Q],
) -> Q:
    if t < 0 or len(defect_upper) != 5 or len(gradient_upper) != 3:
        raise ValueError("invalid rational Galerkin envelope coefficients")
    if t == 0:
        return Q(0)
    integrated_gradient = sum(
        (gradient_upper[j]*t**(j+1)/(j+1) for j in range(3)), Q(0)
    )
    integrated_defect = sum(
        (defect_upper[j]*t**(j+1)/(j+1) for j in range(2, 5)), Q(0)
    )
    return exp_upper(integrated_gradient)*integrated_defect


def certify_run(n: int, phase: int, grid: int, dt: Q) -> dict[str, Any]:
    if (n, phase) not in ROOTS or grid not in GRID_SIZES:
        raise ValueError("unregistered source root or grid")
    if dt not in (COARSE_DT, FINE_DT) or (dt == FINE_DT and grid != 32):
        raise ValueError("unregistered BSAR-15 time step")
    steps = T_END / dt
    if steps.denominator != 1:
        raise ValueError("horizon must be a whole number of steps")

    solver = FourierGalerkin(grid, n, phase)
    poly, defect, _ = taylor_data(n, phase, grid)
    d = [ceil_sqrt(norm_squared(field)) for field in defect]
    g = [gradient_l1(field) for field in poly]
    assert not defect[0] and not defect[1]
    ck = ceil_sqrt(Q(solver.cutoff*(solver.cutoff+1)*(2*solver.cutoff+1)**3))
    field = solver.initial.copy()
    digest = hashlib.sha256()
    rows: list[dict[str, Any]] = []
    for tick in range(steps.numerator+1):
        t = dt*tick
        digest.update(np.ascontiguousarray(field, dtype="<c16").tobytes(order="C"))
        p_t = polynomial_at(poly, t)
        raw = snapshot_reference_distance_upper(solver, field, p_t)
        e_ode = _galerkin_error_upper(t, d, g)
        e_node = raw + e_ode

        # Bounds for the mathematically interpreted real solenoidal field
        # w = Leray(Symmetrize(h_float)). Sym/Leray are L2 contractions.
        # Its source-to-now curl sup is bounded directly by reference
        # drift plus the exact raw-to-reference Fourier norm.
        epsilon_direct = g[1]*t + g[2]*t*t + ck*raw
        core_direct = anchor_certificate_from_epsilon(n, epsilon_direct)

        # Also validate stability through the exact Galerkin path, using
        # BSAR-16B's time-dependent source-relative curl bound.
        epsilon_galerkin = g[1]*t+g[2]*t*t+ck*e_ode
        epsilon_transferred = epsilon_galerkin+ck*e_node
        core_via_galerkin = anchor_certificate_from_epsilon(
            n, epsilon_transferred
        )
        rows.append({
            "time": encode(t),
            "tick": tick,
            "raw_binary64_to_rational_reference_L2_upper": encode(raw),
            "rational_reference_to_exact_galerkin_L2_upper": encode(e_ode),
            "snapshot_to_exact_galerkin_L2_upper": encode(e_node),
            "interpreted_snapshot_core": core_direct,
            "interpreted_snapshot_core_via_galerkin": core_via_galerkin,
        })
        if tick != steps:
            field = solver.step(field, float(dt))

    return {
        "frequency_N": n,
        "phase_sigma": phase,
        "grid_M": grid,
        "cutoff_K": solver.cutoff,
        "dt_nominal_rational": encode(dt),
        "steps": steps.numerator,
        "horizon": encode(T_END),
        "float_state_dtype": "numpy.complex128",
        "float_state_sha256_le_complex128_C": digest.hexdigest(),
        "final_numerical_energy_float64": float(solver.energy(field)),
        "max_node_snapshot_to_exact_galerkin_L2_upper": encode(max(
            Q(x["snapshot_to_exact_galerkin_L2_upper"]) for x in rows
        )),
        "all_nodes_interpreted_core_certified": all(
            x["interpreted_snapshot_core"]["positive_cone_witness_certified"]
            for x in rows
        ),
        "all_nodes_core_via_exact_galerkin_certified": all(
            x["interpreted_snapshot_core_via_galerkin"][
                "positive_cone_witness_certified"
            ] for x in rows
        ),
        "nodes": rows,
    }


def campaign() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    runs = []
    for n, phase in ROOTS:
        for grid in GRID_SIZES:
            runs.append(certify_run(n, phase, grid, COARSE_DT))
        runs.append(certify_run(n, phase, 32, FINE_DT))
    data = json.dumps(runs, sort_keys=True, separators=(",", ":")).encode()
    return runs, {
        "experiment": "BSAR-16D exact-rational a posteriori float64 RK4 time-node audit",
        "run_count": len(runs),
        "snapshot_count": sum(len(x["nodes"]) for x in runs),
        "source_bsar15_module": "experiments.bsar15.galerkin.FourierGalerkin.step",
        "source_bsar14_blob": "aa25ad74be2347acf061d631f55338802eead212",
        "numpy_version": np.__version__,
        "python_version": platform.python_version(),
        "byte_order": sys.byteorder,
        "coordinate_scale": str(COORDINATE_SCALE),
        "norm_scale": str(L2_NORM_SCALE),
        "source_timing": "float64 step(float(Fraction dt)); compare at rational tick*dt",
        "certificate_scope": (
            "All 16 BSAR15 numerical node outputs interpreted as exact binary64 "
            "Fourier tensors; independent Gaussian-rational dense reference; "
            "continuous-time exact Galerkin error via rational Gronwall; "
            "no certified interpolation, FFT physical-grid rounding, or NSE core"
        ),
        "runs_sha256": hashlib.sha256(data).hexdigest(),
    }


def verify_archive(out: Path, *, rerun: bool) -> dict[str, Any]:
    runs_data = (out/"runs.json").read_bytes()
    manifest = json.loads((out/"manifest.json").read_text(encoding="utf-8"))
    rows = json.loads(runs_data)
    if len(rows) != 16 or manifest.get("run_count") != 16:
        raise ValueError("BSAR-16D wrong run count")
    if hashlib.sha256(runs_data).hexdigest() != manifest.get("runs_sha256"):
        raise ValueError("BSAR-16D SHA-256 mismatch")
    if len({(x["frequency_N"],x["phase_sigma"],x["grid_M"],x["dt_nominal_rational"])
            for x in rows}) != 16:
        raise ValueError("BSAR-16D missing or duplicate run")
    if manifest.get("snapshot_count") != sum(len(x["nodes"]) for x in rows):
        raise ValueError("BSAR-16D snapshot count mismatch")
    if rerun:
        expected_rows, expected_manifest = campaign()
        if rows != expected_rows or manifest != expected_manifest:
            raise ValueError("BSAR-16D numerical/rational replay differs")
    return manifest


def freeze(out: Path) -> dict[str, Any]:
    runs, manifest = campaign()
    out.mkdir(parents=True, exist_ok=True)
    data = json.dumps(runs, sort_keys=True, separators=(",", ":")).encode()
    (out/"runs.json").write_bytes(data)
    (out/"manifest.json").write_text(
        json.dumps(manifest, sort_keys=True, indent=2)+"\n", encoding="utf-8"
    )
    verify_archive(out, rerun=False)
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("generate", "audit"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = freeze(args.out) if args.action == "generate" else verify_archive(
        args.out, rerun=True
    )
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

"""BSAR-12: exact two-frequency helical shear Navier–Stokes audit.

For m>=2, N=m^4, s=q/4, A=m^(-q), B=A/8, consider
  u(z,t) = A*exp(-nu*N²*t)*h_N(z) + B*exp(-4nu*N²*t)*h_(2N)(z).
This is a smooth unforced 3D NSE solution since u_z=0 and u depends only
on z. Its vorticity direction generally has nonzero S² covariant tension.

Exact Gaussian rational Fourier identities, a rational nonzero-tension
witness, and energy/cone integral rational inequalities are audited.
Trigonometric/geodesic/exponential steps are proven in the companion
mathematical note, outside the Python exact arithmetic verifier.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

if __package__:
    from .bsar10_beltrami_energy_audit import (
        G, ZERO, IMAGINARY, curl, gauss_dot, modes, vecadd, vecscale, zero_vec,
    )
    from .bsar11_sobolev_critical_audit import (
        BASES, EXPONENT_QUARTERS, VISCOSITIES, HORIZONS, family_parameters,
    )
else:
    from bsar10_beltrami_energy_audit import (
        G, ZERO, IMAGINARY, curl, gauss_dot, modes, vecadd, vecscale, zero_vec,
    )
    from bsar11_sobolev_critical_audit import (
        BASES, EXPONENT_QUARTERS, VISCOSITIES, HORIZONS, family_parameters,
    )

Q = Fraction
BSAR10_COMMIT = "ebcdf96ada525680846a74561ef6ee96be059195"
BSAR11_COMMIT = "90ba30920bc6d6e36dfae94cc1bab7b6eab85ff2"
BSAR09R_COMMIT = "cc1d627d9607234ce4e6ebb41d00b11d1f5725eb"
BSA_R_COMMIT = "80c62433b0eb671175bd8d6169822d3ebd922b60"


def encode(x: Q) -> str:
    return f"{x.numerator}/{x.denominator}"


def exact_fourier(m: int, q: int) -> dict[str, Any]:
    n, a, s = family_parameters(m, q)
    b = a / 8
    modes_a = {k: vecscale(a, v) for k, v in modes(n).items()}
    modes_b = {k: vecscale(b, v) for k, v in modes(2 * n).items()}
    coefficients = {**modes_a, **modes_b}
    zero = zero_vec()
    assert len(coefficients) == 4
    assert (0, 0, 0) not in coefficients

    nonlinear: dict[tuple[int, int, int], tuple[G, G, G]] = {}
    for k, v in coefficients.items():
        assert v[2] == ZERO
        assert gauss_dot(v, k) == ZERO
        assert curl(k, v) == vecscale(-abs(k[2]), v)
        assert k[0] == k[1] == 0
        # Each coefficient has Laplacian -|k|²; time derivative
        # of the corresponding heat-decay coefficient matches nu*Delta.
        assert tuple(x * (-(k[2] * k[2])) for x in v) == vecscale(-(k[2] * k[2]), v)
        for ell, w in coefficients.items():
            key = tuple(x + y for x, y in zip(k, ell))
            contribution = vecscale(IMAGINARY * gauss_dot(v, ell), w)
            nonlinear[key] = vecadd(nonlinear.get(key, zero), contribution)
    assert all(v == zero for v in nonlinear.values())

    l2 = sum(
        (sum((component.magnitude_squared() for component in v), Q(0))
         for v in coefficients.values()),
        Q(0),
    )
    enstrophy = sum(
        (k[2] * k[2] *
         sum((component.magnitude_squared() for component in v), Q(0))
         for k, v in coefficients.items()),
        Q(0),
    )
    assert l2 == a * a + b * b
    assert enstrophy == n * n * (a * a + 4 * b * b)
    assert l2 == Q(65, 64) * a * a

    # 2^(2s)=2^(q/2) is irrational when q is odd. These bounds are
    # exact rational enclosures and do not silently approximate it.
    weight_bounds = {
        0: (Q(1), Q(1)),
        1: (Q(7, 5), Q(3, 2)),
        2: (Q(2), Q(2)),
        3: (Q(14, 5), Q(3)),
        4: (Q(4), Q(4)),
    }
    low, high = weight_bounds[q]
    assert low * low <= 2**q <= high * high
    hs_lower = 1 + low / 64
    hs_upper = 1 + high / 64
    assert Q(1) < hs_lower <= hs_upper <= Q(17, 16)
    assert a * a * m**(2 * q) == 1

    return {
        "frequency": n,
        "mode_count": len(coefficients),
        "amplitude_first": encode(a),
        "amplitude_second": encode(b),
        "s": encode(s),
        "mean_zero": True,
        "divergence_zero": True,
        "zero_nonlinear_advection": True,
        "exact_heat_mode_balance": True,
        "pressure": "0",
        "L2_norm_squared_avg_t0": encode(l2),
        "initial_energy_density": encode(l2 / 2),
        "initial_enstrophy_density": encode(enstrophy),
        "initial_homogeneous_Hs_squared_lower": encode(hs_lower),
        "initial_homogeneous_Hs_squared_upper": encode(hs_upper),
        "initial_Hs_interval_exact_if_even_q": q % 2 == 0,
        "fourier_support": [
            {"k": list(k), "norm_squared": encode(
                sum((c.magnitude_squared() for c in v), Q(0))
            )}
            for k, v in sorted(coefficients.items())
        ],
    }


def conjugate(z: G) -> G:
    return G(z.real, -z.imag)


def tension_witness(n: int, ratio: Q = Q(1, 4)) -> dict[str, Any]:
    """Compute phi'' at theta=pi/2 using exact rational planar vectors.

    The vorticity direction is, up to overall sign,
        (e^(i*theta) + r*e^(2i*theta))/|...|,
    so phi''_z=n² Im[(F''*conj F)*|F|² -
                      (F'*conj F)*(|F|²)'] / |F|^4.
    The displayed expressions are justified by ordinary calculus.
    """
    if n < 1 or not 0 < ratio <= Q(1, 4):
        raise ValueError("Expected n positive and 0<ratio<=1/4")
    r = ratio
    f = G(-r, Q(1))
    fp = G(Q(-1), -2 * r)
    fpp = G(4 * r, Q(-1))
    square = f.magnitude_squared()
    p = fp * conjugate(f)
    pp = fpp * conjugate(f)
    d_square = 2 * p.real
    angular_speed = p.imag / square
    angular_acceleration = (pp.imag * square - p.imag * d_square) / (square * square)
    assert angular_acceleration == -r * (1 - r * r) / ((1 + r * r)**2)
    assert angular_acceleration < 0
    return {
        "angle_theta": "pi/2",
        "ratio_2B_over_A": encode(r),
        "norm_squared": encode(square),
        "direction_angular_velocity_over_n": encode(angular_speed),
        "direction_angular_acceleration_over_n_squared": encode(angular_acceleration),
        "absolute_tension": encode(-angular_acceleration * n * n),
        "positive_tension": True,
        "analytic_scope": "Angle differential formula; exact Gaussian-rational witness",
    }


def bounds(m: int, q: int, nu: Q, horizon: Q, start: Q | None = None) -> dict[str, Any]:
    if nu <= 0 or horizon <= 0:
        raise ValueError("Expected positive nu and horizon")
    n, a, s = family_parameters(m, q)
    if start is None:
        start = horizon / 2
    if start <= 0 or start >= horizon:
        raise ValueError("Expected 0<start<horizon")

    b = a / 8
    initial_r = 2 * b / a
    assert initial_r == Q(1, 4)
    # b_t/a_t=(b/a)*exp(-3nu*n²t) is at most 1/8 at t>=0.
    assert (a - 2 * b) / (a + 2 * b) == Q(3, 5)
    assert (a + 4 * b) / (a - 2 * b) == 2

    x = 2 * nu * n * n * horizon
    scale = a * a * n
    lower = scale / (2 * nu) * x / (1 + x)
    upper = Q(17, 8) * scale / nu
    tail_y = 2 * nu * n * n * start
    tail_upper = Q(17, 8) * scale / (nu * (1 + tail_y))
    uniform_tail_upper = Q(17, 16) / (nu * nu * start)
    assert Q(0) < lower < upper
    assert tail_upper <= uniform_tail_upper
    exponent = 4 - 2 * q
    expected = Q(m**exponent) if exponent >= 0 else Q(1, m**(-exponent))
    assert scale == expected
    assert x < 1 or lower >= scale / (4 * nu)

    return {
        "m": m,
        "q": q,
        "s": encode(s),
        "N": n,
        "A": encode(a),
        "B_over_A_initial": "1/8",
        "nu": encode(nu),
        "T": encode(horizon),
        "start": encode(start),
        "high_vorticity_core_fraction_lower": "3/5",
        "all_points_above_half_peak": True,
        "cone_lower_n": n,
        "cone_upper_4n": 4 * n,
        "x_2nu_n2_T": encode(x),
        "cone_cost_scale_A2N": encode(scale),
        "power_m": exponent,
        "integrated_cone_lower_rational": encode(lower),
        "integrated_cone_upper_rational": encode(upper),
        "positive_start_upper_rational": encode(tail_upper),
        "positive_start_uniform_upper": encode(uniform_tail_upper),
        "if_large_time_lower_at_least_A2N_over_4nu": x < 1 or lower >= scale / (4 * nu),
        "tension_at_z_pi_over_2n": tension_witness(n),
        "status": "exact-Fourier + rational inequalities; geometric and calculus facts in note",
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = []
    for m in BASES:
        for q in EXPONENT_QUARTERS:
            fourier = exact_fourier(m, q)
            sha = hashlib.sha256(
                json.dumps(fourier, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest()
            for nu in VISCOSITIES:
                for t in HORIZONS:
                    row = bounds(m, q, nu, t)
                    row["fourier_sha256"] = sha
                    rows.append(row)
    canonical = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "title": "BSAR-12 exact two-mode helical finite-cone arithmetic receipts",
        "cases": len(rows),
        "bases": list(BASES),
        "exponents_q": list(EXPONENT_QUARTERS),
        "viscosities": [encode(x) for x in VISCOSITIES],
        "horizons": [encode(x) for x in HORIZONS],
        "source_commits": {
            "bsa_r": BSA_R_COMMIT,
            "bsar09r": BSAR09R_COMMIT,
            "bsar10": BSAR10_COMMIT,
            "bsar11": BSAR11_COMMIT,
        },
        "fixed_sobolev_squared_bounds": ["65/64", "17/16"],
        "exact_nonzero_tension_ratio": "60/289",
        "cases_sha256": hashlib.sha256(canonical).hexdigest(),
        "scope": "Exact rational and Fourier certificates; analytic bounds explained in note",
    }
    assert len(rows) == len(BASES) * len(EXPONENT_QUARTERS) * len(VISCOSITIES) * len(HORIZONS)
    return rows, manifest


def audit(out: Path) -> dict[str, Any]:
    rows, manifest = generate()
    observed = [
        json.loads(s)
        for s in (out / "cases.jsonl").read_text(encoding="utf-8").splitlines()
        if s
    ]
    actual_manifest = json.loads((out / "manifest.json").read_text(encoding="utf-8"))
    if observed != rows or actual_manifest != manifest:
        raise ValueError("BSAR-12 exact source or output tampered")
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)
    for cmd in ("generate", "audit"):
        p = sub.add_parser(cmd)
        p.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.cmd == "generate":
        rows, manifest = generate()
        args.out.mkdir(parents=True, exist_ok=True)
        (args.out / "cases.jsonl").write_text(
            "".join(json.dumps(x, sort_keys=True) + "\n" for x in rows), encoding="utf-8"
        )
        (args.out / "manifest.json").write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    else:
        manifest = audit(args.out)
    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

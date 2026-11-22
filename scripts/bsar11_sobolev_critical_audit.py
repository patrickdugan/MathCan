"""BSAR-11: exact Fourier certificates for the critical H^1/2 cone-cost scaling.

For m>=2 and q in {0,1,2,3,4}, choose the exact smooth, unforced,
zero-mean Navier-Stokes solution on (R/2pi Z)^3:

    u = A * exp(-nu*N*N*t) * (cos(N*z), sin(N*z), 0)
    N = m**4, A = m**(-q), homogeneous Sobolev s = q/4.

The *spatial-average squared homogeneous H^s seminorm* is exactly 1 at
t=0 for all m,q. The direction field is independent of the amplitude.
Its exact cone seminorm is between N and 2N. Thus the integrated
K_xi * D cost has the frequency-scale A^2*N/nu = m**(4-2q)/nu,
within universal factors when 2*nu*N^2*T>=1.

The Gaussian-rational Fourier and rational-envelope claims are computed
exactly. The trigonometric bounds and exponential calculus are stated as
analytic lemmas in the research note, not represented as Lean proofs.
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
        G,
        IMAGINARY,
        ZERO,
        curl,
        gauss_dot,
        modes,
        norm_squared_modes,
        vecadd,
        vecscale,
        zero_vec,
    )
else:
    from bsar10_beltrami_energy_audit import (
        G,
        IMAGINARY,
        ZERO,
        curl,
        gauss_dot,
        modes,
        norm_squared_modes,
        vecadd,
        vecscale,
        zero_vec,
    )

Q = Fraction

BASES = (2, 3, 4, 5, 6, 8, 12, 16, 24, 32, 64, 128)
EXPONENT_QUARTERS = (0, 1, 2, 3, 4)
VISCOSITIES = (Q(1, 100), Q(1, 10), Q(1))
HORIZONS = (Q(1, 100), Q(1))
BSAR10_MERGE = "ebcdf96ada525680846a74561ef6ee96be059195"
BSAR09R_MERGE = "cc1d627d9607234ce4e6ebb41d00b11d1f5725eb"
UPSTREAM_SOURCE = "80c62433b0eb671175bd8d6169822d3ebd922b60"


def encode(value: Q) -> str:
    return f"{value.numerator}/{value.denominator}"


def family_parameters(m: int, q: int) -> tuple[int, Q, Q]:
    if m < 2 or q not in EXPONENT_QUARTERS:
        raise ValueError("Expected integer m>=2 and q in 0..4")
    n = m**4
    a = Q(1, m**q)
    s = Q(q, 4)
    return n, a, s


def scaled_fourier(m: int, q: int) -> dict[str, Any]:
    n, a, s = family_parameters(m, q)
    coefficients = {k: vecscale(a, v) for k, v in modes(n).items()}
    origin = (0, 0, 0)
    zero = zero_vec()

    for k, v in coefficients.items():
        assert gauss_dot(v, k) == ZERO, "Nonzero divergence"
        assert curl(k, v) == vecscale(-n, v), "Bad Beltrami eigenvalue"
        assert v[2] == ZERO
    nonlinear = {}
    for p, vp in coefficients.items():
        for k, vk in coefficients.items():
            frequency = tuple(x + y for x, y in zip(p, k))
            nonlinear[frequency] = vecadd(
                nonlinear.get(frequency, zero),
                vecscale(IMAGINARY * gauss_dot(vp, k), vk),
            )
    assert all(v == zero for v in nonlinear.values()), "Nonzero nonlinear advection"
    profile = norm_squared_modes(coefficients)
    gradient = norm_squared_modes(
        {k: vecscale(IMAGINARY * k[2], v) for k, v in coefficients.items()}
    )
    assert profile.get(origin) == G(a * a)
    assert gradient.get(origin) == G(a * a * n * n)
    assert all(k == origin or value == ZERO for k, value in profile.items())
    assert all(k == origin or value == ZERO for k, value in gradient.items())

    # The Fourier multiplier |k|^(2s) is N^(q/2) = m^(2q).
    exact_weight = m ** (2 * q)
    normalized_hs_squared = a * a * exact_weight
    assert normalized_hs_squared == 1
    return {
        "base": m,
        "frequency": n,
        "amplitude": encode(a),
        "regularity_s": encode(s),
        "fourier_multiplier_norm_squared": encode(Q(exact_weight)),
        "initial_homogeneous_Hs_seminorm_squared": encode(normalized_hs_squared),
        "initial_L2_norm_squared": encode(a * a),
        "initial_kinetic_energy_density": encode(a * a / 2),
        "initial_enstrophy_density": encode(a * a * n * n),
        "mean_zero": True,
        "divergence_zero": True,
        "laplacian_eigenvalue": -(n * n),
        "curl_eigenvalue": -n,
        "nonlinear_advection_zero": True,
        "pointwise_velocity_norm_squared": encode(a * a),
        "pointwise_velocity_gradient_squared": encode(a * a * n * n),
        "direction_squared_norm": "1/1",
        "direction_gradient_norm_squared": encode(Q(n * n)),
        "S2_harmonic_map_tension_zero": True,
    }


def exact_envelopes(
    m: int, q: int, viscosity: Q, horizon: Q, positive_start: Q | None = None
) -> dict[str, Any]:
    """Rational bounds proved from the exact Fourier profile plus analytic facts.

    K_xi in [N, 2N] by periodic trigonometry. The integrated cost
    J_{0,T} lies between A²*N/(2nu)*(1-exp(-x)) and
    A²*N/nu*(1-exp(-x)), x=2nu*N²T.

    e^x>=1+x implies the positive rational lower on the full integral.
    The upper bound for the truncated integral follows from
    exp(-y)<=1/(1+y). No floating approximations are computed.
    """
    if viscosity <= 0 or horizon <= 0:
        raise ValueError("Expected positive viscosity and time horizon")
    n, a, s = family_parameters(m, q)
    if positive_start is None:
        positive_start = horizon / 2
    if positive_start <= 0 or positive_start >= horizon:
        raise ValueError("Positive start must lie strictly inside time horizon")

    x = 2 * viscosity * n * n * horizon
    attenuation = x / (1 + x)
    amplitude_sq = a * a
    scale = amplitude_sq * n
    initial_lower = scale / (2 * viscosity) * attenuation
    initial_upper = scale / viscosity
    tail_x = 2 * viscosity * n * n * positive_start
    tail_rational_upper = scale / (viscosity * (1 + tail_x))
    universal_tail_upper = Q(1) / (2 * viscosity * viscosity * positive_start)
    assert Q(0) < initial_lower <= initial_upper
    assert Q(0) < tail_rational_upper <= initial_upper
    assert tail_rational_upper <= universal_tail_upper
    if x >= 1:
        assert initial_lower >= scale / (4 * viscosity)

    exponent = 4 - 2 * q
    assert scale == Q(m**exponent) if exponent >= 0 else scale == Q(1, m**(-exponent))
    return {
        "base": m,
        "regularity_quarters": q,
        "regularity_s": encode(s),
        "frequency": n,
        "amplitude": encode(a),
        "nu": encode(viscosity),
        "T": encode(horizon),
        "positive_start": encode(positive_start),
        "initial_homogeneous_Hs_seminorm_squared": "1/1",
        "dimensionless_cost_power_of_m": exponent,
        "frequency_amplitude_scale": encode(scale),
        "Kxi_lower": n,
        "Kxi_upper": 2 * n,
        "x_2nuN2T": encode(x),
        "initial_cone_integral_lower_rational": encode(initial_lower),
        "initial_cone_integral_upper_rational": encode(initial_upper),
        "positive_start_cone_integral_upper_rational": encode(tail_rational_upper),
        "positive_start_uniform_energy_upper": encode(universal_tail_upper),
        "large_time_gate": x >= 1,
        "if_gate_J_ge_scale_over_4nu": x < 1 or initial_lower >= scale / (4 * viscosity),
        "regime": "diverging" if q < 2 else ("critical" if q == 2 else "decaying"),
        "calculus_scope": "Fourier exact; trigonometry and exp comparison proved in note",
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for m in BASES:
        for q in EXPONENT_QUARTERS:
            fourier = scaled_fourier(m, q)
            source_hash = hashlib.sha256(
                json.dumps(fourier, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest()
            for nu in VISCOSITIES:
                for horizon in HORIZONS:
                    row = exact_envelopes(m, q, nu, horizon)
                    row["fourier_source_sha256"] = source_hash
                    rows.append(row)
    canonical = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "title": "BSAR-11 helical critical Sobolev scaling exact audit",
        "cases": len(rows),
        "bases": list(BASES),
        "quarters": list(EXPONENT_QUARTERS),
        "viscosities": [encode(x) for x in VISCOSITIES],
        "horizons": [encode(x) for x in HORIZONS],
        "source_commits": {
            "bsa_r": UPSTREAM_SOURCE,
            "mathcan_bsar09r": BSAR09R_MERGE,
            "mathcan_bsar10": BSAR10_MERGE,
        },
        "fixed_homogeneous_Hs_norm_squared": "1/1",
        "proof_boundary": "Exact Fourier/Fraction receipt, separate analytic trig/exp derivations",
        "no_trained_model_or_navier_stokes_global_regularty_claim": True,
        "case_sha256": hashlib.sha256(canonical).hexdigest(),
    }
    assert len(rows) == 360
    return rows, manifest


def audit(out: Path) -> dict[str, Any]:
    rows, expected = generate()
    observed_manifest = json.loads((out / "manifest.json").read_text(encoding="utf-8"))
    observed_rows = [
        json.loads(line)
        for line in (out / "cases.jsonl").read_text(encoding="utf-8").splitlines()
        if line
    ]
    if observed_manifest != expected or observed_rows != rows:
        raise ValueError("Exact BSAR-11 archive was altered")
    return expected


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for command in ("generate", "audit"):
        p = sub.add_parser(command)
        p.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    out = args.out
    if args.command == "generate":
        rows, manifest = generate()
        out.mkdir(parents=True, exist_ok=True)
        (out / "cases.jsonl").write_text(
            "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
            encoding="utf-8",
        )
        (out / "manifest.json").write_text(
            json.dumps(manifest, sort_keys=True, indent=2) + "\n", encoding="utf-8"
        )
    else:
        manifest = audit(out)
    print(json.dumps(manifest, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

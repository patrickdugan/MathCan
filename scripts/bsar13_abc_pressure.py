"""BSAR-13: exact ABC flow Fourier pressure balance and cone-cost arithmetic.

The 3D periodic ABC Beltrami field
  U_N=(sin Nz+cos Ny, sin Nx+cos Nz, sin Ny+cos Nx)
has curl U_N=N U_N, div U_N=0 and Delta U_N=-N² U_N.
Therefore u=A e^(-nu N²t) U_N and p=-|u|²/2 solve unforced NSE.
Here (u.grad)u is NONZERO but exactly canceled by grad p.

Gaussian rational Fourier convolution verifies every algebraic identity.
The cone seminorm and exponential integrals use elementary geometric and
calculus lemmas stated in the research note; these are separate from the
source-level exact arithmetic certificates.
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
        G, IMAGINARY, ZERO, curl, gauss_dot, vecadd, vecscale, zero_vec,
    )
    from .bsar11_sobolev_critical_audit import (
        BASES, EXPONENT_QUARTERS, HORIZONS, VISCOSITIES, family_parameters,
    )
else:
    from bsar10_beltrami_energy_audit import (
        G, IMAGINARY, ZERO, curl, gauss_dot, vecadd, vecscale, zero_vec,
    )
    from bsar11_sobolev_critical_audit import (
        BASES, EXPONENT_QUARTERS, HORIZONS, VISCOSITIES, family_parameters,
    )

Q = Fraction
Vec = tuple[G, G, G]
Wave = tuple[int, int, int]
BSAR12_COMMIT = "0faa26a99c3e4a69540a429ed12901ea69bc063b"
BSAR11_COMMIT = "90ba30920bc6d6e36dfae94cc1bab7b6eab85ff2"
BSA_R_COMMIT = "80c62433b0eb671175bd8d6169822d3ebd922b60"


def encode(x: Q) -> str:
    return f"{x.numerator}/{x.denominator}"


def abc_modes(n: int, amplitude: Q) -> dict[Wave, Vec]:
    if n < 1 or amplitude <= 0:
        raise ValueError("Require frequency n>=1 and positive amplitude")
    a = G(amplitude / 2)
    imag = G(Q(0), amplitude / 2)
    return {
        (n, 0, 0): (ZERO, -imag, a),
        (-n, 0, 0): (ZERO, imag, a),
        (0, n, 0): (a, ZERO, -imag),
        (0, -n, 0): (a, ZERO, imag),
        (0, 0, n): (-imag, a, ZERO),
        (0, 0, -n): (imag, a, ZERO),
    }


def dot(a: Vec, b: Vec) -> G:
    output = ZERO
    for x, y in zip(a, b):
        output += x * y
    return output


def fourier_certificate(m: int, q: int) -> dict[str, Any]:
    n, a, s = family_parameters(m, q)
    coeff = abc_modes(n, a)
    zero = zero_vec()
    nonlinear: dict[Wave, Vec] = {}
    pressure: dict[Wave, G] = {}
    for k, v in coeff.items():
        assert gauss_dot(v, k) == ZERO, "Divergence violation"
        assert curl(k, v) == vecscale(n, v), "Not positive-helicity Beltrami"
        assert (k[0]**2 + k[1]**2 + k[2]**2) == n**2
        # Translation by (pi/n,pi/n,pi/n) flips each Fourier mode.
        assert abs(sum(k) // n) == 1
        for ell, w in coeff.items():
            combined = tuple(x + y for x, y in zip(k, ell))
            # (u.grad)u Fourier coefficient Σ (u_k dot i*ell) u_ell
            nonlinear[combined] = vecadd(
                nonlinear.get(combined, zero),
                vecscale(IMAGINARY * gauss_dot(v, ell), w),
            )
            # p=-|u|²/2, so pressure coefficient is -Σ(u_k dot u_ell)/2.
            pressure[combined] = pressure.get(combined, ZERO) + (
                dot(v, w) * Q(-1, 2)
            )

    keys = set(nonlinear) | set(pressure)
    for k in keys:
        pgrad = vecscale(
            IMAGINARY * pressure.get(k, ZERO),
            (G(Q(k[0])), G(Q(k[1])), G(Q(k[2]))),
        )
        assert vecadd(nonlinear.get(k, zero), pgrad) == zero, (
            "Advection and pressure gradient fail to cancel"
        )

    at_origin = zero
    conv_origin = zero
    pressure_gradient_origin = zero
    for k, v in coeff.items():
        at_origin = vecadd(at_origin, v)
    for k in keys:
        conv_origin = vecadd(conv_origin, nonlinear.get(k, zero))
        pressure_gradient_origin = vecadd(
            pressure_gradient_origin,
            vecscale(
                IMAGINARY * pressure.get(k, ZERO),
                (G(Q(k[0])), G(Q(k[1])), G(Q(k[2]))),
            ),
        )
    origin_velocity = (G(a), G(a), G(a))
    origin_nonlin = (G(a*a*n), G(a*a*n), G(a*a*n))
    assert at_origin == origin_velocity
    assert conv_origin == origin_nonlin, "Advection should be nonzero at origin"
    assert pressure_gradient_origin == vecscale(-1, origin_nonlin)

    l2 = sum(
        (sum((c.magnitude_squared() for c in v), Q(0)) for v in coeff.values()),
        Q(0),
    )
    enstrophy = sum(
        ((k[0]**2 + k[1]**2 + k[2]**2) *
         sum((c.magnitude_squared() for c in v), Q(0))
         for k, v in coeff.items()),
        Q(0),
    )
    assert l2 == 3 * a * a
    assert enstrophy == 3 * a * a * n * n
    hs_squared = 3 * a * a * m**(2*q)
    assert hs_squared == 3
    return {
        "frequency": n,
        "amplitude": encode(a),
        "s": encode(s),
        "six_fourier_modes": True,
        "mean_zero": True,
        "divergence_zero": True,
        "curl_eigenvalue": n,
        "laplacian_eigenvalue": -(n*n),
        "nonlinear_advection_nonzero": True,
        "nonlinear_pressure_exact_cancellation": True,
        "advection_at_origin": [encode(x.real) for x in origin_nonlin],
        "pressure_gradient_at_origin": [
            encode(x.real) for x in pressure_gradient_origin
        ],
        "u_at_origin": [encode(x.real) for x in at_origin],
        "sign_reversal_at_pi_over_n_translation": True,
        "mean_L2_squared_initial": encode(l2),
        "mean_energy_initial": encode(l2/2),
        "mean_enstrophy_initial": encode(enstrophy),
        "mean_homogeneous_Hs_squared_initial": encode(hs_squared),
        "source": "exact Gaussian-rational Fourier, no floating PDE residual",
    }


def cone_receipt(m: int, q: int, nu: Q, t: Q, start: Q | None = None) -> dict[str, Any]:
    if nu <= 0 or t <= 0:
        raise ValueError("Require positive nu and horizon")
    n, a, s = family_parameters(m, q)
    if start is None:
        start = t / 2
    if start <= 0 or start >= t:
        raise ValueError("Require 0<start<t")
    x = 2 * nu * n*n * t
    scale = a*a*n

    # Analytic geometric bounds for the high-vorticity core:
    # selected antipodal maximum-core pair gives K_xi >= n/2;
    # global |grad U|_F < 3n and core |U|>=sqrt(3)/2 give K_xi <=24n.
    lower = Q(3, 4) * scale / nu * x/(1+x)
    upper = 36 * scale / nu
    if x >= 1:
        assert lower >= Q(3, 8) * scale / nu

    tail_y = 2 * nu * n*n * start
    tail_bound = 36 * scale / (nu*(1+tail_y))
    global_tail = Q(18) / (nu*nu*start)
    assert tail_bound <= global_tail
    assert lower > 0 and upper > lower
    exponent = 4-2*q
    expected = Q(m**exponent) if exponent >= 0 else Q(1,m**(-exponent))
    assert scale == expected
    return {
        "base": m,
        "q": q,
        "s": encode(s),
        "N": n,
        "A": encode(a),
        "nu": encode(nu),
        "T": encode(t),
        "positive_start": encode(start),
        "mean_homogeneous_Hs_squared_initial": "3/1",
        "high_core_anchor_is_half_peak": True,
        "high_core_antipodal_pair": True,
        "Kxi_lower_N_over_2": encode(Q(n,2)),
        "Kxi_upper_24N": 24*n,
        "x_2nuN2T": encode(x),
        "amplitude_frequency_scale": encode(scale),
        "cost_power_m": exponent,
        "initial_cone_integral_lower_rational": encode(lower),
        "initial_cone_integral_upper_rational": encode(upper),
        "positive_start_cone_upper_rational": encode(tail_bound),
        "positive_start_uniform_upper": encode(global_tail),
        "if_gate_cone_ge_3scale_over_8nu": x < 1 or lower >= Q(3,8)*scale/nu,
        "scope": "Fourier exact; cone geometry, sqrt and exp inequalities in note",
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = []
    for m in BASES:
        for q in EXPONENT_QUARTERS:
            fourier = fourier_certificate(m,q)
            sha = hashlib.sha256(
                json.dumps(fourier,sort_keys=True,separators=(",",":")).encode()
            ).hexdigest()
            for nu in VISCOSITIES:
                for t in HORIZONS:
                    row = cone_receipt(m,q,nu,t)
                    row["fourier_sha256"] = sha
                    rows.append(row)
    receipt={
        "title":"BSAR-13 exact ABC pressure-balanced Beltrami Fourier and cone budget",
        "cases":len(rows),
        "source_commits":{
            "bsa_r":BSA_R_COMMIT,
            "bsar11":BSAR11_COMMIT,
            "bsar12":BSAR12_COMMIT,
        },
        "bases":list(BASES),
        "qs":list(EXPONENT_QUARTERS),
        "viscosities":[encode(nu) for nu in VISCOSITIES],
        "horizons":[encode(t) for t in HORIZONS],
        "Hs_squared_initial":"3/1",
        "nonlinear_advection_zero":False,
        "pressure_exactly_cancels_advection":True,
        "scope":"exact Gaussian Fourier plus rational inequalities; not a Lean PDE proof",
        "rows_sha256":hashlib.sha256(
            json.dumps(rows,sort_keys=True,separators=(",",":")).encode()
        ).hexdigest(),
    }
    assert len(rows)==360
    return rows,receipt


def audit(root:Path)->dict[str,Any]:
    expected,receipt=generate()
    observed=[json.loads(x) for x in (root/"cases.jsonl").read_text().splitlines() if x]
    meta=json.loads((root/"manifest.json").read_text())
    if expected!=observed or meta!=receipt:
        raise ValueError("BSAR-13 archive source or receipts modified")
    return receipt


def main()->int:
    p=argparse.ArgumentParser(description=__doc__)
    subs=p.add_subparsers(dest="command",required=True)
    for command in ("generate","audit"):
        sub=subs.add_parser(command)
        sub.add_argument("--out",type=Path,required=True)
    args=p.parse_args()
    if args.command=="generate":
        rows,meta=generate()
        args.out.mkdir(parents=True,exist_ok=True)
        (args.out/"cases.jsonl").write_text(
            "".join(json.dumps(r,sort_keys=True)+"\n" for r in rows),encoding="utf-8"
        )
        (args.out/"manifest.json").write_text(
            json.dumps(meta,sort_keys=True,indent=2)+"\n",encoding="utf-8"
        )
    else:
        meta=audit(args.out)
    print(json.dumps(meta,sort_keys=True,indent=2))
    return 0


if __name__=="__main__":
    raise SystemExit(main())

"""BSAR-14: exact 3D Fourier triad transfer and time-zero cone diagnostic.

An 8-coefficient divergence-free initial condition at t=0 is encoded as
Gaussian rationals on the 2π-periodic 3-torus. The exact NSE initial
derivative has nonzero Leray-projected nonlinear advection and genuine
inter-shell energy exchange, with pressure reconstructed by Fourier
Poisson inversion.

This is an initial state of a locally smooth 3D Navier–Stokes solution,
NOT a finite-mode exact solution for t>0. The global direction and
geometric cone brackets are derived in the accompanying research note.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any

if __package__:
    from .bsar10_beltrami_energy_audit import (
        G, IMAGINARY, ZERO, curl, gauss_dot, vecadd, vecscale, zero_vec,
    )
    from .bsar11_sobolev_critical_audit import (
        BASES, EXPONENT_QUARTERS, VISCOSITIES, family_parameters,
    )
else:
    from bsar10_beltrami_energy_audit import (
        G, IMAGINARY, ZERO, curl, gauss_dot, vecadd, vecscale, zero_vec,
    )
    from bsar11_sobolev_critical_audit import (
        BASES, EXPONENT_QUARTERS, VISCOSITIES, family_parameters,
    )

Q = Fraction
Wave = tuple[int, int, int]
Vec = tuple[G, G, G]

SOURCE_BSAR = "80c62433b0eb671175bd8d6169822d3ebd922b60"
BSAR13_MERGE = "32693a148b2645177100fd4f8c2c5d0e74d50441"
BSAR11_MERGE = "90ba30920bc6d6e36dfae94cc1bab7b6eab85ff2"
PHASES = (-1, 1)
NORMALIZED_SHELLS = (1, 4, 5)


def encode(value: Q) -> str:
    return f"{value.numerator}/{value.denominator}"


def conj(value: G) -> G:
    return G(value.real, -value.imag)


def conjvec(value: Vec) -> Vec:
    return tuple(conj(x) for x in value)  # type: ignore[return-value]


def gdot(left: Vec, right: Vec) -> G:
    result = ZERO
    for x, y in zip(left, right):
        result += x * y
    return result


def inner_real(left: Vec, right: Vec) -> Q:
    return gdot(conjvec(left), right).real


def kplus(left: Wave, right: Wave) -> Wave:
    return tuple(a + b for a, b in zip(left, right))  # type: ignore[return-value]


def kminus(wave: Wave) -> Wave:
    return tuple(-x for x in wave)  # type: ignore[return-value]


def ksq(wave: Wave) -> int:
    return sum(x * x for x in wave)


def modes(n: int, amplitude: Q, phase: int) -> dict[Wave, Vec]:
    """Real Fourier coefficients of the prescribed non-Beltrami initial field."""
    if n < 1 or amplitude <= 0 or phase not in PHASES:
        raise ValueError("Require n>=1, positive amplitude and phase +/-1")
    a = amplitude
    generators: dict[Wave, Vec] = {
        (n, 0, 0): (ZERO, G(a / 2), ZERO),
        (0, 2 * n, 0): (G(a / 2), ZERO, ZERO),
        (n, 2 * n, 0): (
            G(Q(0), -a * phase), G(Q(0), a * phase / 2), ZERO,
        ),
        (0, 0, n): (G(a / 2), ZERO, ZERO),
    }
    out = dict(generators)
    for wave, val in generators.items():
        out[kminus(wave)] = conjvec(val)
    assert len(out) == 8
    for wave, vector in out.items():
        assert gauss_dot(vector, wave) == ZERO
        assert vector[2] == ZERO
    return out


def convolution(coeff: dict[Wave, Vec]) -> dict[Wave, Vec]:
    """Fourier transform of (u . grad)u at t=0."""
    out: dict[Wave, Vec] = {}
    for p, left in coeff.items():
        for q, right in coeff.items():
            combined = kplus(p, q)
            scalar = IMAGINARY * gauss_dot(left, q)
            out[combined] = vecadd(
                out.get(combined, zero_vec()),
                vecscale(scalar, right),
            )
    assert out.get((0, 0, 0), zero_vec()) == zero_vec()
    return out


def pressure_projection(
    nonlinear: dict[Wave, Vec],
) -> tuple[dict[Wave, G], dict[Wave, Vec]]:
    """Solve pressure Poisson coefficient and project onto ker(k dot)."""
    pressure: dict[Wave, G] = {}
    projected: dict[Wave, Vec] = {}
    for wave, v in nonlinear.items():
        if wave == (0, 0, 0):
            assert v == zero_vec()
            continue
        squared = ksq(wave)
        assert squared > 0
        # -|k|² p_k + i (k dot N_k) = 0
        p = (IMAGINARY * gauss_dot(v, wave)) * Q(1, squared)
        pressure[wave] = p
        gradient = vecscale(
            IMAGINARY * p,
            (G(Q(wave[0])), G(Q(wave[1])), G(Q(wave[2]))),
        )
        solenoidal = vecadd(v, gradient)
        assert gauss_dot(solenoidal, wave) == ZERO
        projected[wave] = solenoidal
    for wave, v in projected.items():
        if kminus(wave) in projected:
            assert projected[kminus(wave)] == conjvec(v)
            assert pressure[kminus(wave)] == conj(pressure[wave])
    return pressure, projected


def phase_factor(power: int) -> G:
    return (G(Q(1)), IMAGINARY, G(Q(-1)), -IMAGINARY)[power % 4]


def exact_point(
    coeff: dict[Wave, Vec], n: int, *, x_pi_over_n: bool,
) -> dict[str, Vec | tuple[Vec, Vec, Vec]]:
    """Evaluate fields at x=0 or pi/n, y=0, z=pi/(2n), exactly."""
    velocity = zero_vec()
    vorticity = zero_vec()
    derivs: list[Vec] = [zero_vec(), zero_vec(), zero_vec()]
    for wave, value in coeff.items():
        if any(k % n != 0 for k in wave):
            raise ValueError("Unexpected wavevector off the frequency lattice")
        power = wave[2] // n + (2 * wave[0] // n if x_pi_over_n else 0)
        phase = phase_factor(power)
        velocity = vecadd(velocity, vecscale(phase, value))
        vorticity = vecadd(vorticity, vecscale(phase, curl(wave, value)))
        for j in range(3):
            derivs[j] = vecadd(
                derivs[j], vecscale(IMAGINARY * wave[j] * phase, value),
            )
    assert all(x.imag == 0 for x in velocity + vorticity)
    assert all(x.imag == 0 for v in derivs for x in v)
    return {"velocity": velocity, "vorticity": vorticity, "gradient": tuple(derivs)}


def vortex_stretching(w: Vec, grad: tuple[Vec, Vec, Vec]) -> Vec:
    result = zero_vec()
    for component, derivative in zip(w, grad):
        result = vecadd(result, vecscale(component, derivative))
    return result


def root_bounds(q: int) -> tuple[Q, Q]:
    """Exact rational root enclosures for homogeneous H^(q/4) norms."""
    two = {
        0: (Q(1), Q(1)),
        1: (Q(7, 5), Q(3, 2)),
        2: (Q(2), Q(2)),
        3: (Q(14, 5), Q(3)),
        4: (Q(4), Q(4)),
    }
    five = {
        0: (Q(1), Q(1)),
        1: (Q(7, 5), Q(3, 2)),
        2: (Q(11, 5), Q(9, 4)),
        3: (Q(10, 3), Q(27, 8)),
        4: (Q(5), Q(5)),
    }
    if q not in EXPONENT_QUARTERS:
        raise ValueError("Expected a supported quarter exponent")
    a, b = two[q]
    c, d = five[q]
    assert a*a <= Q(2**q) <= b*b
    assert c**4 <= Q(5**q) <= d**4
    lower, upper = Q(1) + a / 2 + Q(5, 2) * c, Q(1) + b / 2 + Q(5, 2) * d
    assert Q(4) <= lower <= upper <= Q(31, 2)
    return lower, upper


def exact_certificate(m: int, q: int, nu: Q, phase: int) -> dict[str, Any]:
    if nu <= 0:
        raise ValueError("Viscosity must be positive")
    n, amplitude, s = family_parameters(m, q)
    coeff = modes(n, amplitude, phase)
    nlin = convolution(coeff)
    press, proj = pressure_projection(nlin)
    zero = zero_vec()

    shell_energy: dict[int, Q] = defaultdict(Q)
    shell_transfer: dict[int, Q] = defaultdict(Q)
    enstrophy = Q(0)
    for wave, velocity in coeff.items():
        shell = ksq(wave) // (n*n)
        assert ksq(wave) == shell * n*n
        shell_energy[shell] += inner_real(velocity, velocity) / 2
        shell_transfer[shell] -= inner_real(velocity, proj.get(wave, zero))
        curl_velocity = curl(wave, velocity)
        enstrophy += inner_real(curl_velocity, curl_velocity)
    expected_energy = {
        1: amplitude*amplitude / 2,
        4: amplitude*amplitude / 4,
        5: 5 * amplitude*amplitude / 4,
    }
    expected_transfer = {
        1: Q(phase, 4) * amplitude**3 * n,
        4: -phase * amplitude**3 * n,
        5: Q(3*phase, 4) * amplitude**3 * n,
    }
    assert dict(shell_energy) == expected_energy
    assert dict(shell_transfer) == expected_transfer
    assert sum(shell_transfer.values(), Q(0)) == 0
    assert enstrophy == Q(31, 2) * amplitude*amplitude*n*n
    energy = sum(shell_energy.values(), Q(0))
    assert energy == 2 * amplitude*amplitude
    energy_derivative = -nu * enstrophy
    shell_derivative = {
        shell: shell_transfer[shell] - 2*nu*shell*n*n*shell_energy[shell]
        for shell in NORMALIZED_SHELLS
    }
    assert sum(shell_derivative.values(), Q(0)) == energy_derivative

    generated_wave = (n, 0, n)
    target_projected = (
        ZERO, G(Q(0), amplitude*amplitude*n / 4), ZERO,
    )
    assert generated_wave not in coeff
    assert proj.get(generated_wave) == target_projected
    assert press.get(generated_wave, ZERO) == ZERO

    p0 = exact_point(coeff, n, x_pi_over_n=False)
    p1 = exact_point(coeff, n, x_pi_over_n=True)
    w0, w1 = p0["vorticity"], p1["vorticity"]
    assert isinstance(w0, tuple) and isinstance(w1, tuple)
    assert w0 == (ZERO, G(-amplitude*n), G(-5*phase*amplitude*n))
    assert w1 == (ZERO, G(-amplitude*n), G(5*phase*amplitude*n))
    sq0 = inner_real(w0, w0)
    sq1 = inner_real(w1, w1)
    assert sq0 == sq1 == 26*amplitude*amplitude*n*n
    # |omega|² <= 65 A²N² globally. Both anchors exceed one half
    # of this global upper maximum, as 4*26 > 65.
    assert 4*26 > 65
    difference = vecadd(w0, vecscale(-1, w1))
    diff_sq_over_anchor = inner_real(difference, difference) / sq0
    assert diff_sq_over_anchor == Q(50, 13)

    gradient = p0["gradient"]
    assert isinstance(gradient, tuple)
    stretch = vortex_stretching(w0, gradient)
    assert stretch == (
        G(phase*amplitude*amplitude*n*n),
        G(2*phase*amplitude*amplitude*n*n),
        ZERO,
    )
    hs_low, hs_high = root_bounds(q)
    # N=m^4, A=m^-q, s=q/4. Hence A²N^(2s)=1.
    assert amplitude*amplitude*m**(2*q) == Q(1)
    initial_kd_lower = Q(25, 26)*n*enstrophy
    initial_kd_upper = 26*n*enstrophy
    assert initial_kd_lower < initial_kd_upper

    return {
        "m": m,
        "q": q,
        "s": encode(s),
        "nu": encode(nu),
        "phase_sigma": phase,
        "frequency_N": n,
        "amplitude_A": encode(amplitude),
        "mode_count_real_fourier": len(coeff),
        "convective_support_count": len(nlin),
        "pressure_support_count": len(press),
        "projected_support_count": sum(v != zero for v in proj.values()),
        "mean_mode_zero": True,
        "divergence_zero": True,
        "projection_solenoidal": True,
        "pressure_poisson_exact": True,
        "convection_is_not_pure_gradient": True,
        "kinetic_energy_density_initial": encode(energy),
        "enstrophy_density_initial": encode(enstrophy),
        "viscous_total_energy_derivative_initial": encode(energy_derivative),
        "shell_energy": {str(k): encode(v) for k,v in sorted(shell_energy.items())},
        "shell_nonlinear_transfer": {
            str(k): encode(v) for k,v in sorted(shell_transfer.items())
        },
        "shell_total_derivative": {
            str(k): encode(v) for k,v in sorted(shell_derivative.items())
        },
        "nonlinear_transfer_sum": "0/1",
        "new_3D_mode": [n, 0, n],
        "new_3D_mode_solenoidal_derivative_y": encode(-amplitude*amplitude*n / 4),
        "vortex_stretching_at_anchor": [
            encode(x.real) for x in stretch
        ],
        "high_core_anchor_vorticity_sq": encode(sq0),
        "global_vorticity_norm_sq_upper": encode(65*amplitude*amplitude*n*n),
        "anchor_direction_difference_sq": encode(diff_sq_over_anchor),
        "initial_cone_K_lower": encode(Q(25, 26)*n),
        "initial_cone_K_upper": encode(26*n),
        "initial_KD_lower": encode(initial_kd_lower),
        "initial_KD_upper": encode(initial_kd_upper),
        "Hs_squared_lower": encode(hs_low),
        "Hs_squared_upper": encode(hs_high),
        "energy_transfer_direction": "shell4_loses" if phase==1 else "shell4_gains",
        "scope": "Exact t=0 Fourier derivatives; NO finite-mode evolution or integrated PDE budget",
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = []
    for m in BASES:
        for q in EXPONENT_QUARTERS:
            for nu in VISCOSITIES:
                for phase in PHASES:
                    row = exact_certificate(m, q, nu, phase)
                    identity = f"{m}:{q}:{encode(nu)}"
                    row["pair_id"] = hashlib.sha256(identity.encode()).hexdigest()[:20]
                    rows.append(row)
    source = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "title": "BSAR-14 source-aligned 3D NSE initial triad and shell-transfer audit",
        "cases": len(rows),
        "phase_matched_pairs": len(rows)//2,
        "baseline_exact_transfer": {
            "1": "1/4", "4": "-1/1", "5": "3/4",
        },
        "source_commits": {
            "bsa_r_step7": SOURCE_BSAR,
            "bsar13": BSAR13_MERGE,
            "bsar11": BSAR11_MERGE,
        },
        "phase_reversal_preserves_initial_energy": True,
        "phase_reversal_flips_nonlinear_shell_transfer": True,
        "nonzero_leray_projected_interaction": True,
        "genuine_vorticity_stretching_at_t0": True,
        "data_sha256": hashlib.sha256(source).hexdigest(),
        "evidence_scope": "Exact initial Fourier polynomial; future PDE flow not simulated",
    }
    assert len(rows) == len(BASES)*len(EXPONENT_QUARTERS)*len(VISCOSITIES)*2
    assert len(rows) == 360
    return rows, manifest


def audit(path: Path) -> dict[str, Any]:
    expected, manifest = generate()
    rows = [
        json.loads(line)
        for line in (path / "cases.jsonl").read_text(encoding="utf-8").splitlines()
        if line
    ]
    actual = json.loads((path / "manifest.json").read_text(encoding="utf-8"))
    if rows != expected or manifest != actual:
        raise ValueError("BSAR-14 exact evidence archive changed")
    return actual


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)
    for action in ("generate", "audit"):
        p = sub.add_parser(action)
        p.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.cmd == "generate":
        rows, manifest = generate()
        args.out.mkdir(parents=True, exist_ok=True)
        (args.out / "cases.jsonl").write_text(
            "".join(json.dumps(x, sort_keys=True)+"\n" for x in rows),
            encoding="utf-8",
        )
        (args.out / "manifest.json").write_text(
            json.dumps(manifest, indent=2, sort_keys=True)+"\n",
            encoding="utf-8",
        )
    else:
        manifest = audit(args.out)
    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

"""BSAR-16F: exact-rational shell-transfer sign-persistence certificates.

Compute the full degree-six shell-transfer polynomial of the independent
BSAR-16B Taylor field. A shell-local trilinear estimate transfers its
strict rational sign margins to the *exact* continuous Galerkin ODE over
a datum-dependent rational duration.

The certificate does not identify shell transfers of the full NSE PDE,
and the prior float64 RK4 sign observations are not used to choose bounds.
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
    Field,
    Wave,
    cutoff,
    encode,
    ksq,
    pair_real,
    squared_norm,
    validate_field,
    zero_vec,
)
from experiments.bsar16.rational_enclosure import (
    TIME_END,
    ceil_sqrt,
    exp_upper,
    gradient_l1,
    norm_squared,
    polynomial_at,
    projected_product,
    round_up,
    taylor_data,
)

SHELLS = (1, 4, 5)
ENVELOPE_DECIMAL_DIGITS = 12
DISPLAY_SCALE = 10**ENVELOPE_DECIMAL_DIGITS


def shell_modes(n: int, kmax: int, shell: int) -> tuple[Wave, ...]:
    """All actual Fourier lattice points in the registered shell/cube."""
    if n <= 0 or kmax < 0 or shell not in SHELLS:
        raise ValueError("invalid shell/cutoff/frequency")
    modes = tuple(
        (x, y, z)
        for x in range(-kmax, kmax + 1)
        for y in range(-kmax, kmax + 1)
        for z in range(-kmax, kmax + 1)
        if x*x + y*y + z*z == shell*n*n
    )
    if not modes:
        raise ValueError("empty target shell")
    return modes


def shell_transfer(field: Field, n: int, shell: int) -> Q:
    """Exactly evaluate T_shell(field) with the full Leray projector."""
    validate_field(field)
    nonlinear = projected_product(field, field)
    return -sum(
        (pair_real(u, nonlinear.get(k, zero_vec()))
         for k, u in field.items() if ksq(k) == shell*n*n), Q(0)
    )


def convolution_coefficients(coeffs: list[Field]) -> list[Field]:
    """Full exact quadratic Fourier convolution coefficients."""
    if len(coeffs) != 3:
        raise ValueError("expected quadratic rational Taylor reference")
    result: list[Field] = [{} for _ in range(5)]
    for i, ai in enumerate(coeffs):
        for j, aj in enumerate(coeffs):
            term = projected_product(ai, aj)
            for k, v in term.items():
                if k in result[i+j]:
                    from experiments.bsar16.exact_residual import add
                    result[i+j][k] = add(result[i+j][k], v)
                else:
                    result[i+j][k] = v
    return result


def transfer_polynomials(
    coeffs: list[Field], n: int,
) -> dict[int, tuple[Q, ...]]:
    """Gaussian-rational degree <= 6 shell-transfer polynomials."""
    nonlinear = convolution_coefficients(coeffs)
    result: dict[int, tuple[Q, ...]] = {}
    for shell in SHELLS:
        values: list[Q] = [Q(0) for _ in range(7)]
        for i, velocity in enumerate(coeffs):
            for j, forcing in enumerate(nonlinear):
                values[i+j] -= sum(
                    (pair_real(u, forcing.get(k, zero_vec()))
                     for k, u in velocity.items()
                     if ksq(k) == shell*n*n), Q(0)
                )
        result[shell] = tuple(values)
    return result


def evaluate(coefficients: tuple[Q, ...], t: Q) -> Q:
    """Horner evaluation with exact rational coefficients."""
    if t < 0:
        raise ValueError("nonnegative time required")
    value = Q(0)
    for coefficient in reversed(coefficients):
        value = coefficient + t*value
    return value


def reference_sign_margin(coefficients: tuple[Q, ...], horizon: Q) -> Q:
    """Valid lower signed value on EVERY t in [0,horizon].

    If sign(c0)>0, each signed c_j t^j is at least
    min(0,sign(c0)*c_j)*horizon^j.
    """
    if not coefficients or coefficients[0] == 0 or horizon < 0:
        raise ValueError("nonzero time-zero transfer and nonnegative horizon required")
    sign = 1 if coefficients[0] > 0 else -1
    return abs(coefficients[0]) + sum(
        (min(Q(0), sign*c)*horizon**j
         for j, c in enumerate(coefficients[1:], 1)), Q(0)
    )


def shell_gradient_l1(field: Field, n: int, shell: int) -> Q:
    """Rational upper bound on ||grad Q_shell a_j||_infty."""
    return sum(
        (ceil_sqrt(Q(ksq(k))*squared_norm(v))
         for k, v in field.items() if ksq(k) == shell*n*n), Q(0)
    )


def rational_error_at(
    horizon: Q, g: tuple[Q, Q, Q], d: tuple[Q, Q, Q, Q, Q],
    exponential_subdivisions: int,
) -> Q:
    """Monotone-in-horizon version of BSAR-16B's Galerkin L2 bound.

    Use a *fixed* exponential rational upper function with n selected at
    the maximum registered T. Then every term is monotone on [0,T].
    """
    if horizon < 0 or horizon > TIME_END:
        raise ValueError("horizon outside the registered validation window")
    if exponential_subdivisions < 1:
        raise ValueError("positive exponential subdivision required")
    if horizon == 0:
        return Q(0)
    integrated_gradient = sum(
        (g[j]*horizon**(j+1)/(j+1) for j in range(3)), Q(0)
    )
    integrated_defect = sum(
        (d[j]*horizon**(j+1)/(j+1) for j in range(2, 5)), Q(0)
    )
    n = exponential_subdivisions
    if integrated_gradient/n > Q(1, 2):
        raise ValueError("exponential grid does not cover the horizon")
    return (Q(1)-integrated_gradient/n)**(-n)*integrated_defect


def _fixed_exponential_subdivisions(g: tuple[Q, Q, Q]) -> int:
    total = sum(
        (g[j]*TIME_END**(j+1)/(j+1) for j in range(3)), Q(0)
    )
    n = 1
    while total/n > Q(1, 2):
        n *= 2
    return n


def shell_trilinear_error(
    y: Q, p_bound: Q, shell_gradient_bound: Q, shell_constant: Q,
) -> Q:
    """Prove |T_s(v)-T_s(p)| <= this bound for ||v-p||_2<=y.

    Periodic incompressibility moves the derivative in B(b,c)
    onto Q_shell a. For tau_s(a,b,c)=<Q_s a,B(b,c)>,
    |tau_s(a,b,c)| <= ||grad Q_s a||_infty ||b||_2 ||c||_2.

    For error e, ||grad Q_s e||_infty <= sqrt(#modes*s*N^2)||e||_2.
    The seven terms of tau_s(p+e,p+e,p+e)-tau_s(p,p,p) are all kept.
    """
    if min(y, p_bound, shell_gradient_bound, shell_constant) < 0:
        raise ValueError("nonnegative bounds required")
    return (
        y*(shell_constant*p_bound*p_bound+2*shell_gradient_bound*p_bound)
        + y*y*(2*shell_constant*p_bound+shell_gradient_bound)
        + shell_constant*y*y*y
    )


def _basis(n: int, phase: int, grid: int) -> dict[str, Any]:
    if (n, phase) not in ROOTS or grid not in GRID_SIZES:
        raise ValueError("unregistered root/grid")
    kmax = cutoff(grid)
    polynomial, defect, _ = taylor_data(n, phase, grid, VISCOSITY)
    for a in polynomial:
        validate_field(a, kmax)
    transfers = transfer_polynomials(polynomial, n)
    expected = {
        1: Q(phase*n, 4),
        4: Q(-phase*n),
        5: Q(3*phase*n, 4),
    }
    for shell in SHELLS:
        if transfers[shell][0] != expected[shell]:
            raise ValueError("BSAR-14 exact transfer source mismatch")
    g = tuple(gradient_l1(x) for x in polynomial)
    d = tuple(ceil_sqrt(norm_squared(x)) for x in defect)
    p = tuple(ceil_sqrt(norm_squared(x)) for x in polynomial)
    assert len(g) == len(p) == 3 and len(d) == 5
    assert d[0] == d[1] == 0
    exp_n = _fixed_exponential_subdivisions(g)
    return {
        "polynomial": polynomial,
        "transfers": transfers,
        "g": g,
        "d": d,
        "p": p,
        "exp_n": exp_n,
        "cutoff": kmax,
    }


def _enclosure_terms(
    basis: dict[str, Any], n: int, shell: int, horizon: Q,
) -> tuple[Q, Q, Q, Q, Q, int]:
    poly: list[Field] = basis["polynomial"]
    c = basis["transfers"][shell]
    kmax = basis["cutoff"]
    count = len(shell_modes(n, kmax, shell))
    cs = ceil_sqrt(Q(shell*n*n*count))
    y = rational_error_at(horizon, basis["g"], basis["d"], basis["exp_n"])
    p = sum(
        (basis["p"][j]*horizon**j for j in range(3)), Q(0)
    )
    shell_grad = sum(
        (shell_gradient_l1(poly[j], n, shell)*horizon**j
         for j in range(3)), Q(0)
    )
    error = shell_trilinear_error(y, p, shell_grad, cs)
    refmargin = reference_sign_margin(c, horizon)
    return refmargin-error, refmargin, error, y, cs, count


def certify_shell(
    basis: dict[str, Any], n: int, shell: int,
    max_horizon: Q = TIME_END,
) -> dict[str, Any]:
    if shell not in SHELLS or max_horizon <= 0 or max_horizon > TIME_END:
        raise ValueError("invalid requested shell/window")
    signed_margin, ref, error, y, cs, count = _enclosure_terms(
        basis, n, shell, max_horizon
    )
    duration = max_horizon
    if signed_margin <= 0:
        # Rational dyadic subdivision. The error majorant is nondecreasing
        # with t and the signed polynomial lower bound nonincreasing.
        # Find a strictly positive certified interval of length >= T/2^20.
        found = False
        for j in range(1, 21):
            candidate = max_horizon/(2**j)
            signed_margin, ref, error, y, cs, count = _enclosure_terms(
                basis, n, shell, candidate
            )
            if signed_margin > 0:
                duration = candidate
                found = True
                break
        if not found:
            raise ArithmeticError("no positive certified dyadic duration")
    return {
        "shell_normalized": shell,
        "initial_transfer": encode(basis["transfers"][shell][0]),
        "exact_transfer_polynomial_coefficients": [
            encode(x) for x in basis["transfers"][shell]
        ],
        "shell_lattice_mode_count": count,
        "shell_gradient_error_constant_upper": encode(cs),
        "certified_duration": encode(duration),
        "full_registered_T_certified": duration == TIME_END,
        "reference_signed_transfer_lower": encode(round_up(Q(0)) if ref < 0 else
                                                 Q((ref.numerator*DISPLAY_SCALE)//ref.denominator, DISPLAY_SCALE)),
        "galerkin_transfer_difference_upper": encode(round_up(error, DISPLAY_SCALE)),
        "final_signed_transfer_lower": encode(
            Q((signed_margin.numerator*DISPLAY_SCALE)//signed_margin.denominator,
              DISPLAY_SCALE)
        ),
        "galerkin_L2_error_upper_at_duration": encode(round_up(y, DISPLAY_SCALE)),
        "certification": "exact rational polynomial + shell-local trilinear + fixed-exp rational Gronwall",
    }


def certify(n: int, phase: int, grid: int) -> dict[str, Any]:
    basis = _basis(n, phase, grid)
    rows = [certify_shell(basis, n, shell) for shell in SHELLS]
    return {
        "frequency_N": n,
        "phase_sigma": phase,
        "grid_M": grid,
        "retained_cube_cutoff_K": cutoff(grid),
        "registered_horizon": encode(TIME_END),
        "exact_taylor_degree": 2,
        "shell_polynomial_degree_at_most": 6,
        "rational_exponential_subdivisions": basis["exp_n"],
        "all_shell_signs_certified_through_T": all(
            r["full_registered_T_certified"] for r in rows
        ),
        "shells": rows,
        "scope": (
            "Exact continuous finite Galerkin ODE sign preservation for the "
            "specified rational duration; no full NSE shell-transfer proof"
        ),
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = [certify(n, phase, grid) for n, phase in ROOTS for grid in GRID_SIZES]
    serialized = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "experiment": "BSAR-16F exact rational Galerkin shell sign persistence",
        "case_count": len(rows),
        "shell_certificate_count": sum(len(row["shells"]) for row in rows),
        "full_window_sign_cases": sum(row["all_shell_signs_certified_through_T"] for row in rows),
        "source_exact_mathcan": SOURCE_MATHCAN,
        "source_bsar14_blob": SOURCE_BSAR14_BLOB,
        "source_bsa_r": SOURCE_BSAR,
        "viscosity": encode(VISCOSITY),
        "window": encode(TIME_END),
        "precision": "Gaussian-rational polynomial + upward 1e-9 square-root bounds",
        "conservation_boundary": "Exact finite Galerkin only, not full NSE or measured RK4",
        "rows_sha256": hashlib.sha256(serialized).hexdigest(),
    }
    return rows, manifest


def freeze(out: Path) -> dict[str, Any]:
    rows, manifest = generate()
    out.mkdir(parents=True, exist_ok=True)
    (out/"rows.json").write_bytes(
        json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    )
    (out/"manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True)+"\n", encoding="utf-8"
    )
    return manifest


def audit(out: Path) -> dict[str, Any]:
    expected_rows, expected_manifest = generate()
    observed_rows = json.loads((out/"rows.json").read_text(encoding="utf-8"))
    observed_manifest = json.loads((out/"manifest.json").read_text(encoding="utf-8"))
    if observed_rows != expected_rows or observed_manifest != expected_manifest:
        raise ValueError("BSAR-16F exact shell-sign rational archive changed")
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

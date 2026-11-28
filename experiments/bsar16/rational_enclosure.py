"""BSAR-16B: rational degree-two dense trajectory and a priori error enclosures.

No floating-point arithmetic is used in the certificates. A quadratic Taylor
polynomial p(t) with Gaussian-rational Fourier coefficients approximates the
*exact* finite-dimensional Galerkin ODE. Its continuous-time defect is a
degree-four polynomial whose L2 coefficients are evaluated exactly. An energy
estimate and a one-sided convective bound enclose the exact Galerkin path.

This independent validated reference is NOT a roundoff certificate for the
BSAR-15 NumPy RK4 trajectories and NOT an unconditional full-NSE error proof.
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
    I,
    Q,
    VISCOSITY,
    Field,
    add,
    cutoff,
    encode,
    exact_decomposition,
    kdot,
    ksq,
    leray,
    scale,
    source_modes,
    squared_norm,
    validate_field,
    zero_vec,
)

TIME_END = Q(3, 250)
ROUNDING_SCALE = 10**9


def cleaned(field: Field) -> Field:
    return {k: v for k, v in field.items() if v != zero_vec()}


def add_field(left: Field, right: Field) -> Field:
    out = dict(left)
    for k, v in right.items():
        out[k] = add(out.get(k, zero_vec()), v)
    return cleaned(out)


def scale_field(field: Field, scalar: Q | int) -> Field:
    return cleaned({k: scale(scalar, v) for k, v in field.items()})


def laplacian_field(field: Field, nu: Q) -> Field:
    """The linear Galerkin contribution -nu*|k|^2*v_k."""
    return cleaned({k: scale(-nu*ksq(k), v) for k, v in field.items()})


def projected_product(a: Field, b: Field) -> Field:
    """Compute P[(a dot grad)b] using exact *unaliased* convolution."""
    out: Field = {}
    for p, ap in a.items():
        for q, bq in b.items():
            term = scale(I * kdot(ap, q), bq)
            if term == zero_vec():
                continue
            k = tuple(i+j for i, j in zip(p, q))
            out[k] = add(out.get(k, zero_vec()), term)
    return cleaned(leray(cleaned(out)))


def projected_split(a: Field, b: Field, kmax: int) -> tuple[Field, Field]:
    all_modes = projected_product(a, b)
    low = {k: v for k, v in all_modes.items()
           if max(abs(j) for j in k) <= kmax}
    high = {k: v for k, v in all_modes.items()
            if max(abs(j) for j in k) > kmax}
    return low, high


def rhs_polynomial(coeffs: list[Field], kmax: int, nu: Q) -> list[Field]:
    """Coefficients F_j of F(sum_i a_i*t^i), j=0,...,2*degree."""
    degree = len(coeffs)-1
    out: list[Field] = []
    for j in range(2*degree+1):
        value = laplacian_field(coeffs[j], nu) if j <= degree else {}
        for i in range(max(0, j-degree), min(degree, j)+1):
            low, _ = projected_split(coeffs[i], coeffs[j-i], kmax)
            value = add_field(value, scale_field(low, -1))
        out.append(value)
    return out


def high_polynomial(coeffs: list[Field], kmax: int) -> list[Field]:
    degree = len(coeffs)-1
    result: list[Field] = []
    for j in range(2*degree+1):
        high: Field = {}
        for i in range(max(0, j-degree), min(degree, j)+1):
            _, term = projected_split(coeffs[i], coeffs[j-i], kmax)
            high = add_field(high, term)
        result.append(high)
    return result


def taylor_data(
    n: int, phase: int, grid: int, nu: Q = VISCOSITY,
) -> tuple[list[Field], list[Field], list[Field]]:
    """Return rational p(t), defect p'-F(p), and high forcing P_>K B(p,p)."""
    kmax = cutoff(grid)
    source = source_modes(n, phase)
    validate_field(source, kmax)
    if nu <= 0:
        raise ValueError("positive viscosity required")
    f0 = rhs_polynomial([source], kmax, nu)[0]
    first_rhs = rhs_polynomial([source, f0], kmax, nu)
    a2 = scale_field(first_rhs[1], Q(1, 2))
    polynomial = [source, f0, a2]
    rhs_coeffs = rhs_polynomial(polynomial, kmax, nu)
    defect: list[Field] = []
    for j, f_j in enumerate(rhs_coeffs):
        derivative = scale_field(polynomial[j+1], j+1) if j+1 < 3 else {}
        defect.append(add_field(derivative, scale_field(f_j, -1)))
    assert not defect[0] and not defect[1], "Taylor matching failed"
    residual = high_polynomial(polynomial, kmax)
    return polynomial, defect, residual


def norm_squared(field: Field) -> Q:
    return sum((squared_norm(v) for v in field.values()), Q(0))


def ceil_sqrt(q: Q, scale: int = ROUNDING_SCALE) -> Q:
    """Outward rational upper bound on sqrt(q), with no floating point."""
    if q < 0 or scale <= 0:
        raise ValueError("expected nonnegative rational and positive scale")
    if q == 0:
        return Q(0)
    n = (q.numerator*scale*scale + q.denominator-1)//q.denominator
    root = isqrt(n)
    if root*root < n:
        root += 1
    out = Q(root, scale)
    assert out*out >= q
    return out


def round_up(q: Q, scale: int = ROUNDING_SCALE) -> Q:
    if q < 0 or scale <= 0:
        raise ValueError("expected nonnegative rational and positive scale")
    return Q((q.numerator*scale + q.denominator-1)//q.denominator, scale)


def coeff_l1(field: Field) -> Q:
    return sum((ceil_sqrt(squared_norm(v)) for v in field.values()), Q(0))


def gradient_l1(field: Field) -> Q:
    # The operator norm of (v_hat(k) outer k) is |v_hat(k)|*|k|.
    return sum(
        (ceil_sqrt(Q(ksq(k))*squared_norm(v)) for k, v in field.items()),
        Q(0),
    )


def polynomial_at(coeffs: list[Field], t: Q) -> Field:
    if t < 0:
        raise ValueError("nonnegative time required")
    out: Field = {}
    for j, term in enumerate(coeffs):
        out = add_field(out, scale_field(term, t**j))
    return out


def exp_upper(q: Q) -> Q:
    """e^q <= (1-q/n)^(-n), with an exact rational rhs and q/n <= 1/2."""
    if q < 0:
        raise ValueError("nonnegative exponent required")
    n = 1
    while q/Q(n) > Q(1, 2):
        n *= 2
    upper = (Q(1)-q/n)**(-n)
    assert upper >= Q(1)
    return upper


def enclosure(
    n: int, phase: int, grid: int, horizon: Q = TIME_END,
    nu: Q = VISCOSITY,
) -> dict[str, Any]:
    if horizon <= 0:
        raise ValueError("positive time horizon required")
    if nu <= 0:
        raise ValueError("positive viscosity required")
    kmax = cutoff(grid)
    poly, defect, high = taylor_data(n, phase, grid, nu)
    d = [ceil_sqrt(norm_squared(a)) for a in defect]
    r = [ceil_sqrt(norm_squared(a)) for a in high]
    g = [gradient_l1(a) for a in poly]
    s = [coeff_l1(a) for a in poly]

    # For e=v_Galerkin-p, energy cancellation gives
    # d/dt ||e||_2 <= ||grad p||_infty ||e||_2 + ||p'-F(p)||_2.
    # Grad p <= g0+t*g1+t^2*g2; defect <= d2*t^2+d3*t^3+d4*t^4.
    integrated_grad = sum(
        (g[j]*horizon**(j+1)/(j+1) for j in range(3)), Q(0)
    )
    integrated_defect = sum(
        (d[j]*horizon**(j+1)/(j+1) for j in range(2, 5)), Q(0)
    )
    finite_ode_error = exp_upper(integrated_grad)*integrated_defect

    # Exact Galerkin energy decreases: ||v||_2 <= ||v(0)||_2 = 2.
    # Bound B(e,v) by ||e||_infty ||grad v||_2 and B(p,e) by
    # ||p||_infty ||grad e||_2. Fourier Cauchy-Schwarz:
    # ||e||_infty <= sqrt(number of modes) ||e||_2.
    source_norm = Q(2)
    m = (2*kmax+1)**3-1
    wave_upper = ceil_sqrt(Q(3*kmax*kmax))
    sup_p = sum((s[j]*horizon**j for j in range(3)), Q(0))
    high_error_lipschitz = (
        source_norm*ceil_sqrt(Q(3*kmax*kmax*m))
        + sup_p*wave_upper
    )
    residual_bound = (
        sum((r[j]*horizon**j for j in range(5)), Q(0))
        + high_error_lipschitz*finite_ode_error
    )

    # ||grad e||_infty <= sqrt(sum_{k in Lambda_K}|k|^2) ||e||_2.
    # sum_{k in Lambda_K}|k|^2 = K(K+1)(2K+1)^3 exactly.
    gradient_error_lipschitz = ceil_sqrt(
        Q(kmax*(kmax+1)*(2*kmax+1)**3)
    )
    gradient_bound = (
        sum((g[j]*horizon**j for j in range(3)), Q(0))
        + gradient_error_lipschitz*finite_ode_error
    )

    # Conditional: a smooth full 3D NSE solution u exists on [0,T].
    # ||u(T)-v(T)|| <= T*max ||r_K|| exp(T*max ||grad v_K||).
    conditional_pde_error = (
        horizon*residual_bound*exp_upper(horizon*gradient_bound)
    )
    initial = exact_decomposition(poly[0], kmax, nu)
    assert initial["high_residual_l2_squared"] == norm_squared(high[0])
    assert norm_squared(poly[0]) == Q(4)
    assert not defect[0] and not defect[1]

    return {
        "frequency_N": n,
        "phase_sigma": phase,
        "grid_M": grid,
        "retained_cube_cutoff_K": kmax,
        "viscosity": encode(nu),
        "time_horizon": encode(horizon),
        "polynomial_degree": 2,
        "defect_first_nonzero_degree_at_least": 2,
        "source_initial_L2_squared": "4/1",
        "initial_high_residual_L2_squared": encode(norm_squared(high[0])),
        "taylor_coefficients_support_counts": [len(a) for a in poly],
        "defect_upper_coefficients": [encode(x) for x in d[2:]],
        "residual_upper_coefficients": [encode(x) for x in r],
        "integrated_reference_gradient_upper": encode(round_up(integrated_grad)),
        "integrated_defect_upper": encode(round_up(integrated_defect)),
        "validated_galerkin_L2_error_upper": encode(round_up(finite_ode_error)),
        "validated_time_uniform_residual_L2_upper": encode(round_up(residual_bound)),
        "validated_time_uniform_gradient_Linfty_upper": encode(round_up(gradient_bound)),
        "conditional_true_NSE_L2_error_upper_at_T": encode(
            round_up(conditional_pde_error)
        ),
        "numeric_precision": "Gaussian-rational exact, square-root upper 1e-9, rational exponential upper",
        "scope": (
            "Validated rational Taylor-2 reference versus exact Galerkin ODE; "
            "full-NSE L2 bound conditional on smooth existence; BSAR-15 RK4 "
            "float trajectory and vorticity core remain uncertified"
        ),
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = [enclosure(n, phase, grid) for n, phase in ROOTS for grid in GRID_SIZES]
    data = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    return rows, {
        "experiment": "BSAR-16B rational Taylor-2 dense Galerkin enclosure",
        "cases": len(rows),
        "source_exact_mathcan": SOURCE_MATHCAN,
        "source_bsar14_blob": SOURCE_BSAR14_BLOB,
        "source_bsa_r": SOURCE_BSAR,
        "viscosity": encode(VISCOSITY),
        "time_horizon": encode(TIME_END),
        "normalization": "Fourier coefficients on 2pi-periodic torus; mean L2",
        "validation": "exact rational polynomial defect, energy bound, analytic comparison",
        "not_validated": "BSAR-15 NumPy RK4 trajectory; unconditional NSE; vorticity core",
        "rows_sha256": hashlib.sha256(data).hexdigest(),
    }


def freeze(out: Path) -> dict[str, Any]:
    rows, manifest = generate()
    out.mkdir(parents=True, exist_ok=True)
    data = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    (out / "rows.json").write_bytes(data)
    (out / "manifest.json").write_text(
        json.dumps(manifest, sort_keys=True, indent=2)+"\n", encoding="utf-8"
    )
    return manifest


def audit(out: Path) -> dict[str, Any]:
    expected, manifest = generate()
    rows = json.loads((out / "rows.json").read_text(encoding="utf-8"))
    observed = json.loads((out / "manifest.json").read_text(encoding="utf-8"))
    if expected != rows or observed != manifest:
        raise ValueError("BSAR-16B rational enclosure changed")
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

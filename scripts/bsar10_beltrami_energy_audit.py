"""BSAR-10: exact periodic helical Navier-Stokes Fourier certificate.

This standard-library checker validates a family of *actual smooth unforced
Navier-Stokes solutions* on the three-dimensional 2π-periodic torus:

    u_N(x,y,z,t) = exp(-nu*N*N*t) (cos(N*z), sin(N*z), 0),  p = 0.

It uses Gaussian rationals to prove Fourier-mode algebra exactly, with no
finite differences or unverified floating-point PDE residuals.

Analytic facts in the accompanying note (calculus, periodic distance and
exp convexity) are explicit external mathematical premises. The checker
supplies rational lower-bound receipts, not a formal PDE Lean theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

SOURCE_COMMIT = "80c62433b0eb671175bd8d6169822d3ebd922b60"
MATHCAN_BSAR09R = "cc1d627d9607234ce4e6ebb41d00b11d1f5725eb"
FREQUENCIES = (*range(1, 65), 128, 256, 512, 1024, 2048)
VISCOSITIES = (Fraction(1, 100), Fraction(1, 10), Fraction(1))
HORIZONS = (Fraction(1, 100), Fraction(1))

Q = Fraction
Wavevector = tuple[int, int, int]


@dataclass(frozen=True)
class G:
    """A Gaussian rational, a + i*b, with exact operations."""

    real: Q = Q(0)
    imag: Q = Q(0)

    def __add__(self, other: G) -> G:
        return G(self.real + other.real, self.imag + other.imag)

    def __neg__(self) -> G:
        return G(-self.real, -self.imag)

    def __mul__(self, other: G | Q | int) -> G:
        if not isinstance(other, G):
            other = G(Q(other))
        return G(
            self.real * other.real - self.imag * other.imag,
            self.real * other.imag + self.imag * other.real,
        )

    def magnitude_squared(self) -> Q:
        return self.real * self.real + self.imag * self.imag


ZERO = G()
IMAGINARY = G(Q(0), Q(1))
Vec = tuple[G, G, G]


def vecscale(scalar: G | Q | int, vector: Vec) -> Vec:
    return tuple((v * scalar for v in vector))  # type: ignore[return-value]


def vecadd(left: Vec, right: Vec) -> Vec:
    return tuple((a + b for a, b in zip(left, right)))  # type: ignore[return-value]


def gauss_dot(vector: Vec, k: Wavevector) -> G:
    result = ZERO
    for component, direction in zip(vector, k):
        result += component * direction
    return result


def zero_vec() -> Vec:
    return (ZERO, ZERO, ZERO)


def modes(n: int) -> dict[Wavevector, Vec]:
    if n < 1:
        raise ValueError("Periodic helical frequency must be a positive integer")
    return {
        (0, 0, n): (G(Q(1, 2)), G(Q(0), Q(-1, 2)), ZERO),
        (0, 0, -n): (G(Q(1, 2)), G(Q(0), Q(1, 2)), ZERO),
    }


def curl(k: Wavevector, v: Vec) -> Vec:
    x, y, z = k
    cross = (
        v[2] * y + -(v[1] * z),
        v[0] * z + -(v[2] * x),
        v[1] * x + -(v[0] * y),
    )
    return vecscale(IMAGINARY, cross)


def norm_squared_modes(field: dict[Wavevector, Vec]) -> dict[Wavevector, G]:
    """Fourier coefficients of the pointwise squared norm.

    The field coefficients satisfy the usual reality condition,
    so Fourier multiplication is bilinear, without a conjugate.
    This checks *pointwise* constant speed and gradient norm.
    """
    result: dict[Wavevector, G] = {}
    for p, a in field.items():
        for q, b in field.items():
            k = tuple(x + y for x, y in zip(p, q))
            coefficient = ZERO
            for x, y in zip(a, b):
                coefficient += x * y
            result[k] = result.get(k, ZERO) + coefficient
    return result


def check_fourier(n: int) -> dict[str, Any]:
    """Exact Fourier check of mean, divergence, curl, Laplacian, and advection."""
    coefficients = modes(n)
    zero = zero_vec()
    for k, v in coefficients.items():
        assert gauss_dot(v, k) == ZERO, "A nonzero Fourier divergence"
        assert curl(k, v) == vecscale(-n, v), "Not a negative Beltrami mode"
        assert k[0] * k[0] + k[1] * k[1] + k[2] * k[2] == n * n
        assert v[2] == ZERO, "The field must have zero vertical component"

    # Fourier transform of (u · grad)u:
    # each interaction p+q receives (u_hat[p] · i*q) u_hat[q].
    nonlinear: dict[Wavevector, Vec] = {}
    for p, a in coefficients.items():
        for q, b in coefficients.items():
            k = tuple(x + y for x, y in zip(p, q))
            coefficient = vecscale(IMAGINARY * gauss_dot(a, q), b)
            nonlinear[k] = vecadd(nonlinear.get(k, zero), coefficient)
    assert all(value == zero for value in nonlinear.values()), "Nonlinear term nonzero"

    profile_sq = norm_squared_modes(coefficients)
    vertical_derivative = {
        k: vecscale(IMAGINARY * k[2], v) for k, v in coefficients.items()
    }
    derivative_sq = norm_squared_modes(vertical_derivative)
    zero_frequency = (0, 0, 0)
    assert profile_sq.get(zero_frequency) == G(Q(1))
    assert derivative_sq.get(zero_frequency) == G(Q(n * n))
    assert all(k == zero_frequency or value == ZERO for k, value in profile_sq.items())
    assert all(k == zero_frequency or value == ZERO for k, value in derivative_sq.items())
    # For xi=-u_profile, Delta xi=-n^2 xi and |grad xi|^2=n^2,
    # hence the covariant S^2 harmonic-map tension is identically zero.

    avg_u_squared = sum(
        (sum((component.magnitude_squared() for component in v), Q(0))
         for v in coefficients.values()),
        Q(0),
    )
    avg_omega_squared = n * n * avg_u_squared
    assert avg_u_squared == 1 and avg_omega_squared == n * n

    return {
        "frequency": n,
        "mean_zero": (0, 0, 0) not in coefficients,
        "divergence_zero": True,
        "curl_eigenvalue": -n,
        "laplacian_eigenvalue": -(n * n),
        "nonlinear_advection_zero": True,
        "profile_pointwise_norm_squared": "1/1",
        "profile_pointwise_gradient_squared": str(n * n),
        "direction_harmonic_map_tension_zero": True,
        "pressure": "0",
        "velocity_norm_sq_spatial_average_t0": "1/1",
        "vorticity_norm_sq_spatial_average_t0": str(avg_omega_squared),
        "modes": [
            {"wavevector": list(k), "fourier_weight_sq":
             str(sum((v_.magnitude_squared() for v_ in v), Q(0)))}
            for k, v in sorted(coefficients.items())
        ],
    }


def encode(value: Q) -> str:
    return f"{value.numerator}/{value.denominator}"


def exact_lower_receipt(n: int, viscosity: Q, horizon: Q) -> dict[str, Any]:
    """A rational *lower* bound on the integrated direction-cost proxy.

    With normalized torus volume, D(t)=n² exp(-2νn²t), and
    K_xi(t) >= 4n/π >= n (using π<4).

    Convexity e^x >= 1+x gives 1-e^(-x) >= x/(1+x)
    for x=2νn²T >=0. Hence
      ∫ K_xi D dt >= n/(2ν) * x/(1+x).

    No transcendental approximation is needed for this certificate.
    """
    if n < 1 or viscosity <= 0 or horizon <= 0:
        raise ValueError("Expected n>=1, viscosity>0, horizon>0")
    x = 2 * viscosity * n * n * horizon
    lower_factor = x / (1 + x)
    lower_cone_integral = Q(n, 1) / (2 * viscosity) * lower_factor
    assert lower_factor >= 0
    assert lower_cone_integral > 0

    # ν∫||∇u||² dt = (1-e^-x)/2 <= 1/2 exactly, since x>=0.
    # The exact integral is not evaluated here; this is its analytic ceiling.
    return {
        "frequency": n,
        "nu": encode(viscosity),
        "T": encode(horizon),
        "x_equals_2nu_n2_T": encode(x),
        "initial_kinetic_energy_density": "1/2",
        "viscous_dissipation_upper": "1/2",
        "initial_enstrophy_density": encode(Q(n * n)),
        "direction_seminorm_lower": encode(Q(n)),
        "integrated_Kxi_D_lower_rational": encode(lower_cone_integral),
        "high_frequency_gate_2nu_n2_T_ge_1": x >= 1,
        "if_gate_then_integrated_Kxi_D_ge_n_over_4nu": (
            x < 1 or lower_cone_integral >= Q(n) / (4 * viscosity)
        ),
        "scope": "Exact Gaussian-Fourier and rational lower bound; calculus stated in note",
    }


def digest(rows: list[dict[str, Any]]) -> str:
    data = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = []
    for n in FREQUENCIES:
        fourier = check_fourier(n)
        for nu in VISCOSITIES:
            for horizon in HORIZONS:
                row = exact_lower_receipt(n, nu, horizon)
                row["source_commit"] = SOURCE_COMMIT
                row["mathcan_prior"] = MATHCAN_BSAR09R
                row["fourier_identity_sha256"] = hashlib.sha256(
                    json.dumps(fourier, sort_keys=True).encode("utf-8")
                ).hexdigest()
                rows.append(row)
    if len(rows) != len(FREQUENCIES) * len(VISCOSITIES) * len(HORIZONS):
        raise AssertionError("Unexpected generated case count")
    manifest = {
        "generator": "BSAR-10 exact helical Fourier and rational energy-only obstruction",
        "cases": len(rows),
        "source_commit": SOURCE_COMMIT,
        "prior_mathcan_commit": MATHCAN_BSAR09R,
        "spatial_average_domain": "T3=(R/2πZ)^3, volume-normalized",
        "smooth_unforced_solution": "u_n=e^(-nu*n^2*t)*(cos(n*z),sin(n*z),0)",
        "energy0_density": "1/2",
        "case_sha256": digest(rows),
        "analysis_gate": "All-time analytic lower bound on Kxi uses π<4 and e^x>=1+x",
        "disclaimer": (
            "No uniform Kxi*enstrophy integral cap follows solely from initial "
            "kinetic energy. Every individual mode is smooth and has finite integral."
        ),
    }
    return rows, manifest


def validate(rows: list[dict[str, Any]], manifest: dict[str, Any]) -> None:
    expected, original = generate()
    if rows != expected or manifest != original:
        raise ValueError("Altered exact Fourier corpus or arithmetic receipt")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="cmd", required=True)
    gen = sub.add_parser("generate")
    gen.add_argument("--out", required=True, type=Path)
    audit = sub.add_parser("audit")
    audit.add_argument("--out", required=True, type=Path)
    args = p.parse_args()
    folder = args.out
    if args.cmd == "generate":
        folder.mkdir(parents=True, exist_ok=True)
        rows, manifest = generate()
        (folder / "cases.jsonl").write_text(
            "".join(json.dumps(r, sort_keys=True) + "\n" for r in rows),
            encoding="utf-8",
        )
        (folder / "manifest.json").write_text(
            json.dumps(manifest, sort_keys=True, indent=2) + "\n", encoding="utf-8"
        )
    else:
        rows = [
            json.loads(line)
            for line in (folder / "cases.jsonl").read_text(encoding="utf-8").splitlines()
            if line
        ]
        manifest = json.loads((folder / "manifest.json").read_text(encoding="utf-8"))
        validate(rows, manifest)
    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

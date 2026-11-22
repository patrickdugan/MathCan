"""BSAR-16A: exact Fourier spatial residual of the BSAR-14 datum.

The calculations are rational. They concern the exact initial datum and the
finite Galerkin vector field, NOT the floating RK4 trajectory or a validated
Navier--Stokes time evolution. Coefficients use normalized Fourier series on
(2*pi periodic)^3 and spatial-average L2 norms.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

Q = Fraction
Wave = tuple[int, int, int]


@dataclass(frozen=True)
class Gaussian:
    real: Q = Q(0)
    imag: Q = Q(0)

    def __add__(self, other: Gaussian) -> Gaussian:
        return Gaussian(self.real + other.real, self.imag + other.imag)

    def __neg__(self) -> Gaussian:
        return Gaussian(-self.real, -self.imag)

    def __sub__(self, other: Gaussian) -> Gaussian:
        return self + -other

    def __mul__(self, other: Gaussian | Q | int) -> Gaussian:
        if not isinstance(other, Gaussian):
            other = Gaussian(Q(other))
        return Gaussian(
            self.real * other.real - self.imag * other.imag,
            self.real * other.imag + self.imag * other.real,
        )

    def conjugate(self) -> Gaussian:
        return Gaussian(self.real, -self.imag)

    def squared_modulus(self) -> Q:
        return self.real**2 + self.imag**2


ZERO = Gaussian()
I = Gaussian(Q(0), Q(1))
Vec = tuple[Gaussian, Gaussian, Gaussian]
Field = dict[Wave, Vec]
GRID_SIZES = (16, 24, 32)
ROOTS = ((1, -1), (1, 1), (2, -1), (2, 1))
VISCOSITY = Q(1, 10)
SOURCE_MATHCAN = "e2c0e1c56f6e5d2291536156709f75668d1e0f8f"
SOURCE_BSAR14_BLOB = "aa25ad74be2347acf061d631f55338802eead212"
SOURCE_BSAR = "80c62433b0eb671175bd8d6169822d3ebd922b60"


def add(a: Vec, b: Vec) -> Vec:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def scale(a: Gaussian | Q | int, v: Vec) -> Vec:
    return tuple(x * a for x in v)  # type: ignore[return-value]


def dot(a: Vec, b: Vec) -> Gaussian:
    return sum_gauss(x * y for x, y in zip(a, b))


def sum_gauss(values: Any) -> Gaussian:
    result = ZERO
    for value in values:
        result = result + value
    return result


def kdot(a: Vec, k: Wave) -> Gaussian:
    return sum_gauss(x * j for x, j in zip(a, k))


def minus(k: Wave) -> Wave:
    return tuple(-j for j in k)  # type: ignore[return-value]


def opposite(v: Vec) -> Vec:
    return tuple(x.conjugate() for x in v)  # type: ignore[return-value]


def zero_vec() -> Vec:
    return (ZERO, ZERO, ZERO)


def squared_norm(v: Vec) -> Q:
    return sum((x.squared_modulus() for x in v), Q(0))


def pair_real(a: Vec, b: Vec) -> Q:
    return dot(opposite(a), b).real


def ksq(k: Wave) -> int:
    return sum(j*j for j in k)


def cutoff(grid: int) -> int:
    if grid < 12 or grid % 4:
        raise ValueError("require a supported grid divisible by four")
    return (grid - 1) // 3


def source_modes(n: int, phase: int, a: Q = Q(1)) -> Field:
    """Independently encode the eight BSAR-14 Gaussian-rational modes."""
    if n < 1 or phase not in (-1, 1) or a <= 0:
        raise ValueError("invalid source frequency, phase, or amplitude")
    generators: Field = {
        (n, 0, 0): (ZERO, Gaussian(a/2), ZERO),
        (0, 2*n, 0): (Gaussian(a/2), ZERO, ZERO),
        (n, 2*n, 0): (Gaussian(Q(0), -a*phase),
                        Gaussian(Q(0), a*phase/2), ZERO),
        (0, 0, n): (Gaussian(a/2), ZERO, ZERO),
    }
    out = dict(generators)
    for k, v in generators.items():
        out[minus(k)] = opposite(v)
    validate_field(out)
    return out


def validate_field(field: Field, kmax: int | None = None) -> None:
    if kmax is not None and kmax < 0:
        raise ValueError("cutoff must be nonnegative")
    for k, v in field.items():
        if len(k) != 3 or len(v) != 3:
            raise ValueError("expected three-dimensional coefficients")
        if k == (0, 0, 0) and v != zero_vec():
            raise ValueError("the mean must vanish")
        if kmax is not None and max(abs(j) for j in k) > kmax:
            raise ValueError("field contains a mode outside Galerkin cube")
        if kdot(v, k) != ZERO:
            raise ValueError("field is not divergence free")
        if field.get(minus(k), zero_vec()) != opposite(v):
            raise ValueError("field violates Fourier reality")


def nonlinear(field: Field) -> Field:
    """Exact unaliased coefficients of (u dot grad)u."""
    validate_field(field)
    out: Field = {}
    for p, up in field.items():
        for q, uq in field.items():
            k = tuple(a+b for a, b in zip(p, q))
            interaction = scale(I * kdot(up, q), uq)
            out[k] = add(out.get(k, zero_vec()), interaction)
    assert out.get((0, 0, 0), zero_vec()) == zero_vec()
    return out


def leray(field: Field) -> Field:
    """Project every nonzero wavevector with exact rational arithmetic."""
    out: Field = {}
    for k, v in field.items():
        if k == (0, 0, 0):
            if v != zero_vec():
                raise ValueError("unexpected nonzero mean forcing")
            continue
        correction = kdot(v, k) * Q(1, ksq(k))
        out[k] = tuple(x - correction * j for x, j in zip(v, k))  # type: ignore[assignment]
        assert kdot(out[k], k) == ZERO
    return out


def exact_decomposition(field: Field, kmax: int, nu: Q = VISCOSITY) -> dict[str, Any]:
    """Exact P_<=K/P_>K split, kinetic-energy algebra, and forcing norm."""
    validate_field(field, kmax)
    if nu <= 0:
        raise ValueError("viscosity must be positive")
    projected = leray(nonlinear(field))
    high = {
        k: v for k, v in projected.items()
        if max(abs(j) for j in k) > kmax and v != zero_vec()
    }
    low = {
        k: v for k, v in projected.items()
        if max(abs(j) for j in k) <= kmax and v != zero_vec()
    }
    energy = sum((squared_norm(v) for v in field.values()), Q(0)) / 2
    dissipation = sum((ksq(k)*squared_norm(v) for k, v in field.items()), Q(0))
    nonlinear_power = sum(
        (pair_real(u, low.get(k, zero_vec())) for k, u in field.items()), Q(0)
    )
    # dE/dt = <u, -P_<=K B(u,u)-nu*(-Delta)u> in normalized L2.
    derivative = -nonlinear_power - nu*dissipation
    high_sq = sum((squared_norm(v) for v in high.values()), Q(0))
    return {
        "kinetic_energy": energy,
        "dissipation": dissipation,
        "nonlinear_energy_power": nonlinear_power,
        "energy_derivative": derivative,
        "high_residual_l2_squared": high_sq,
        "high_residual": high,
        "low_projected": low,
    }


def encode(q: Q) -> str:
    return f"{q.numerator}/{q.denominator}"


def encode_vec(v: Vec) -> list[list[str]]:
    return [[encode(x.real), encode(x.imag)] for x in v]


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for n, phase in ROOTS:
        field = source_modes(n, phase)
        for grid in GRID_SIZES:
            kmax = cutoff(grid)
            result = exact_decomposition(field, kmax)
            assert result["kinetic_energy"] == Q(2)
            assert result["dissipation"] == Q(31, 2)*n*n
            assert result["nonlinear_energy_power"] == 0
            assert result["energy_derivative"] == -VISCOSITY*Q(31, 2)*n*n
            assert (result["high_residual_l2_squared"] > 0) == (
                n == 2 and grid in (16, 24)
            )
            high = result["high_residual"]
            rows.append({
                "frequency_N": n,
                "phase_sigma": phase,
                "grid_M": grid,
                "retained_cube_cutoff_K": kmax,
                "source_mode_count": len(field),
                "kinetic_energy": encode(result["kinetic_energy"]),
                "enstrophy_D": encode(result["dissipation"]),
                "exact_nonlinear_energy_power": encode(result["nonlinear_energy_power"]),
                "exact_energy_derivative": encode(result["energy_derivative"]),
                "high_residual_l2_squared": encode(result["high_residual_l2_squared"]),
                "high_residual_mode_count": len(high),
                "high_residual_coefficients": [
                    {"k": list(k), "projected_convection": encode_vec(v)}
                    for k, v in sorted(high.items())
                ],
                "scope": "exact time-zero rational Fourier polynomial only",
            })
    data = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "experiment": "BSAR-16A exact initial Fourier-truncation residual",
        "cases": len(rows),
        "root_count": len(ROOTS),
        "source_exact_mathcan": SOURCE_MATHCAN,
        "source_bsar14_blob": SOURCE_BSAR14_BLOB,
        "source_bsa_r": SOURCE_BSAR,
        "viscosity": encode(VISCOSITY),
        "fourier_convention": "u(x)=sum u_hat(k) exp(i k.x); normalized torus mean-square",
        "residual_definition": "P_>K P[(u_K dot grad)u_K] at t=0",
        "evidence_scope": "exact rational t=0; no certified RK4/global PDE error",
        "rows_sha256": hashlib.sha256(data).hexdigest(),
    }
    return rows, manifest


def freeze(out: Path) -> dict[str, Any]:
    rows, manifest = generate()
    out.mkdir(parents=True, exist_ok=True)
    (out / "rows.json").write_bytes(
        json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    )
    (out / "manifest.json").write_text(
        json.dumps(manifest, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )
    return manifest


def audit(out: Path) -> dict[str, Any]:
    expected, manifest = generate()
    rows = json.loads((out / "rows.json").read_text(encoding="utf-8"))
    saved = json.loads((out / "manifest.json").read_text(encoding="utf-8"))
    if expected != rows or manifest != saved:
        raise ValueError("BSAR-16A exact residual evidence changed")
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("generate", "audit"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(freeze(args.out) if args.action == "generate"
                     else audit(args.out), sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

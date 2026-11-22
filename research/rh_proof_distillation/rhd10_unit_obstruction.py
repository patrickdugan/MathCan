"""RHD-10C: exact cyclotomic-unit obstruction to single-place 29-ramification.

All computations live in (Z/29^2)[alpha]/(f_j(alpha)) for the four
Hensel-lifted factors of Phi_20. This is finite arithmetic, not a
formal Lean proof of class field theory or automorphic representation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from research.rh_proof_distillation.rhd09_local_character import (
    P, P2, dirichlet_exponent, lifted_factors,
)

FACTORS = lifted_factors()
RESIDUE_UNITS_EXPONENT = P * P - 1  # |F_{29^2}^x| = 840
UNIT_EXPONENTS = (1, 3)
PHI20_AT_ONE = 1


def mul(f: tuple[int, int, int], u: tuple[int, int],
        v: tuple[int, int]) -> tuple[int, int]:
    """Multiply a+b*alpha in the quadratic quotient, modulo 29^2."""
    a, b = u
    d, e = v
    return ((a*d - f[0]*b*e) % P2,
            (a*e + b*d - f[1]*b*e) % P2)


def power(f: tuple[int, int, int], u: tuple[int, int],
          exponent: int) -> tuple[int, int]:
    if exponent < 0:
        raise ValueError("negative exponent unsupported")
    answer = (1, 0)
    while exponent:
        if exponent & 1:
            answer = mul(f, answer, u)
        u = mul(f, u, u)
        exponent >>= 1
    return answer


def local_norm(f: tuple[int, int, int], u: tuple[int, int]) -> int:
    a, b = u
    return (a*a - f[1]*a*b + f[0]*b*b) % P2


def cyclotomic_unit(f: tuple[int, int, int], k: int) -> tuple[int, int]:
    """The localization of the actual algebraic unit 1-zeta_20^k."""
    a, b = power(f, (0, 1), k)
    return ((1 - a) % P2, (-b) % P2)


def principal_log_vector(f: tuple[int, int, int],
                         unit: tuple[int, int]) -> tuple[int, int]:
    """Canonical mod-29 first-layer log vector of a local unit.

    u^840 = 1-29*z (mod 841), since 840=-1 (mod 29).
    Thus z = (1-u^840)/29 (mod 29), with two F_29 coordinates.
    """
    x, y = power(f, unit, RESIDUE_UNITS_EXPONENT)
    if x % P != 1 or y % P != 0:
        raise ValueError("input is not an invertible local unit")
    assert (1 - x) % P == 0 and y % P == 0
    return (((1 - x) // P) % P, ((-y) // P) % P)


def determinant(u: tuple[int, int], v: tuple[int, int]) -> int:
    return (u[0]*v[1] - u[1]*v[0]) % P


def obstruction_receipt() -> dict:
    """Two global units span every local first-layer logarithm space."""
    if PHI20_AT_ONE != 1:
        raise AssertionError("cyclotomic-unit norm premise failed")
    places = []
    norm_products = [1, 1]
    character_sums = [0, 0]
    for j, f in enumerate(FACTORS):
        units = [cyclotomic_unit(f, k) for k in UNIT_EXPONENTS]
        norms = [local_norm(f, u) for u in units]
        if any(n % P == 0 for n in norms):
            raise AssertionError("1-zeta^k must be a local unit")
        logs = [principal_log_vector(f, u) for u in units]
        det = determinant(*logs)
        if det == 0:
            raise AssertionError("units do not span local first layer")
        exponents = [dirichlet_exponent(n) for n in norms]
        for t in range(len(UNIT_EXPONENTS)):
            norm_products[t] = norm_products[t] * norms[t] % P2
            character_sums[t] = (character_sums[t] + exponents[t]) % P
        places.append({
            "factor_index": j,
            "factor_mod_841": list(f),
            "unit_norms": norms,
            "unit_log_vectors": [list(x) for x in logs],
            "determinant_mod_29": det,
            "local_norm_character_exponents": exponents,
        })
    if norm_products != [1, 1] or character_sums != [0, 0]:
        raise AssertionError("global unit norm/product compatibility failed")
    return {
        "experiment": "RHD-10C exact single-place order-29 unit obstruction",
        "field": "Q(zeta_20)",
        "prime": P,
        "modulus": P2,
        "unit_exponents": list(UNIT_EXPONENTS),
        "unit_norms_globally": norm_products,
        "local_character_sums_mod_29": character_sums,
        "places": places,
        "statement_scope": (
            "Finite-order characters of exact order 29, trivial infinity type, "
            "unramified away from one selected prime; first principal-unit layer"
        ),
        "lean_witness_proved": False,
        "automorphic_witness_proved": False,
    }


def write_report(path: Path) -> dict:
    report = obstruction_receipt()
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = (json.dumps(report, sort_keys=True, indent=2) + "\n").encode()
    path.write_bytes(encoded)
    path.with_suffix(".sha256").write_text(
        hashlib.sha256(encoded).hexdigest() + "  " + path.name + "\n")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(write_report(args.output), sort_keys=True, indent=2))

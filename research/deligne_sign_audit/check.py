"""Exact finite-field shadow models for the Deligne sign-only proof audit.

This module treats F_p^d for p=2,3. Character sums with integer weights are
represented in Z[zeta_p], so every reported inequality is checked over Z.
No etale-cohomology or general weight theorem is asserted by these tests.
"""

from itertools import product
from math import prod


def vectors(p: int, d: int):
    if p not in (2, 3) or d < 1:
        raise ValueError("exact cyclotomic evaluator supports p in {2,3}, d>=1")
    return tuple(product(range(p), repeat=d))


def identity_matrix(d: int):
    return tuple(tuple(int(i == j) for j in range(d)) for i in range(d))


def bilinear(x, y, matrix, p: int) -> int:
    return sum(x[i] * matrix[i][j] * y[j]
               for i in range(len(x)) for j in range(len(y))) % p


def character_coefficients(p: int, d: int, weights, matrix=None):
    """Return C_a for sum weight(x) zeta_p^phase(x) = sum C_a zeta_p^a."""
    k = len(weights)
    if k < 2:
        raise ValueError("path length k must be >=2")
    if matrix is None:
        matrix = identity_matrix(d)
    space = vectors(p, d)
    if any(set(w) != set(space) for w in weights):
        raise ValueError("all weights must be defined on F_p^d")
    if len(matrix) != d or any(len(row) != d for row in matrix):
        raise ValueError("matrix shape must equal d x d")
    coeffs = [0] * p
    for path in product(space, repeat=k):
        term = prod(weights[i][path[i]] for i in range(k))
        exponent = sum(bilinear(path[i], path[i + 1], matrix, p)
                       for i in range(k - 1)) % p
        coeffs[exponent] += term
    return tuple(coeffs)


def exact_norm_squared(p: int, coeffs) -> int:
    """Absolute-square in Z[zeta_p] for p in {2,3}."""
    if p == 2 and len(coeffs) == 2:
        return (coeffs[0] - coeffs[1]) ** 2
    if p == 3 and len(coeffs) == 3:
        a, b = coeffs[0] - coeffs[2], coeffs[1] - coeffs[2]
        return a * a - a * b + b * b
    raise ValueError("p must be 2 or 3 with p coefficients")


def verify_path_bound(p: int, d: int, weights, matrix=None) -> dict:
    """Check |S|^2 <= T^(2k) * p^(d(k+1)) exactly."""
    k = len(weights)
    t = max(abs(v) for w in weights for v in w.values())
    coeffs = character_coefficients(p, d, weights, matrix)
    squared = exact_norm_squared(p, coeffs)
    ceiling = t ** (2 * k) * p ** (d * (k + 1))
    return {"ok": squared <= ceiling, "norm2": squared,
            "ceiling": ceiling, "coeffs": coeffs}


def verify_fourier_orthogonality(p: int, d: int, matrix=None) -> bool:
    """Check K K* = p^d I from exact root-of-unity sums."""
    space = vectors(p, d)
    if matrix is None:
        matrix = identity_matrix(d)
    for x in space:
        for xp in space:
            delta = tuple((a - b) % p for a, b in zip(x, xp))
            coeffs = [0] * p
            for y in space:
                coeffs[bilinear(delta, y, matrix, p)] += 1
            target = p ** (2 * d) if x == xp else 0
            if exact_norm_squared(p, coeffs) != target:
                return False
    return True


def hyperbola_count(p: int, a: int, b: int, c: int) -> int:
    """Count xy+ax+by+c=0 over F_p by enumeration."""
    return sum((x * y + a * x + b * y + c) % p == 0
               for x in range(p) for y in range(p))


def hyperbola_sign_receipt(p: int, a: int, b: int, c: int) -> dict:
    """Example 5: U=A1, X=A2, M=p, N=p-1 when ab!=c."""
    n = hyperbola_count(p, a, b, c)
    r = p * n - p ** 2
    return {"smooth": (a * b - c) % p != 0,
            "N": n, "M": p, "R": r, "signedR": -r}


def all_unit_weights(p: int, d: int, k: int):
    return tuple({x: 1 for x in vectors(p, d)} for _ in range(k))

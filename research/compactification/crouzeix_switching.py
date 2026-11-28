"""Exact-rational arithmetic for the NRF-01 pure-math switching theorem.

Finite identities are checked; the external Crouzeix theorem is cited rather
than claimed to have been independently verified.
"""
from fractions import Fraction as Q
from itertools import product


def jordan_disk_upper(shear: Q, coefficients: tuple[Q, ...]) -> Q:
    """Exact triangle upper bound on sup_{z in W(A)}|p(z)|."""
    if not coefficients:
        raise ValueError("nonempty polynomial")
    radius = abs(shear) / 2
    return sum((abs(a) * radius**k for k, a in enumerate(coefficients)), Q(0))


def phase_factor(eta: Q, q_bound: Q) -> Q:
    if not 0 <= eta <= 1 or q_bound < 0:
        raise ValueError("requires eta in [0,1], q>=0")
    return (1 - eta) + 2 * eta * q_bound


def amplification(rates: tuple[Q, ...]) -> Q:
    v = Q(1)
    for rate in rates:
        if rate < 0:
            raise ValueError("negative rate")
        v *= rate
    return v


def weighted_disturbance(rates: tuple[Q, ...], deltas: tuple[Q, ...]) -> Q:
    """sum_j delta_j product_{ell>j} rate_ell."""
    if len(rates) != len(deltas) or any(d < 0 for d in deltas):
        raise ValueError("bad disturbance schedule")
    return sum((d * amplification(rates[j+1:]) for j, d in enumerate(deltas)), Q(0))


def recursive_disturbance(rates: tuple[Q, ...], deltas: tuple[Q, ...]) -> Q:
    if len(rates) != len(deltas):
        raise ValueError("bad disturbance schedule")
    current = Q(0)
    for r, d in zip(rates, deltas):
        if r < 0 or d < 0:
            raise ValueError("negative rate or disturbance")
        current = r * current + d
    return current


def cycles_disturbance(rates: tuple[Q, ...], deltas: tuple[Q, ...], cycles: int) -> Q:
    if cycles < 0:
        raise ValueError("negative cycle count")
    gamma = amplification(rates)
    if gamma >= 1:
        raise ValueError("cycle not contractive")
    d = weighted_disturbance(rates, deltas)
    return d * (1 - gamma**cycles) / (1 - gamma)


def exact_jordan_polynomial(shear: Q, coeff: tuple[Q, ...]) -> tuple[tuple[Q, Q], tuple[Q, Q]]:
    """Return p(cI+shear E12) in the centered (z-c) basis."""
    a0, a1 = coeff[0], coeff[1] if len(coeff) > 1 else Q(0)
    return ((a0, a1 * shear), (Q(0), a0))


def two_by_two_pow(m: tuple[tuple[Q, Q], tuple[Q, Q]], n: int):
    if n < 0:
        raise ValueError("negative degree")
    result = ((Q(1), Q(0)), (Q(0), Q(1)))
    for _ in range(n):
        result = tuple(tuple(sum((result[i][k] * m[k][j] for k in range(2)), Q(0))
                              for j in range(2)) for i in range(2))
    return result


def independent_jordan_eval(shear: Q, coeff: tuple[Q, ...]):
    matrix = ((Q(0), shear), (Q(0), Q(0)))
    out = [[Q(0), Q(0)], [Q(0), Q(0)]]
    for k, a in enumerate(coeff):
        p = two_by_two_pow(matrix, k)
        for i, j in product(range(2), repeat=2):
            out[i][j] += a * p[i][j]
    return tuple(tuple(row) for row in out)

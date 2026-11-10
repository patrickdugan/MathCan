"""Exact rational certificates for frictional directed exchange cycles.

These are abstract marginal-rate networks, without trade size, market impact,
reserve changes or transaction ordering.
"""
from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class IntervalEdge:
    source: int
    target: int
    lower: Fraction
    upper: Fraction

    def __post_init__(self):
        if not (0 < self.lower <= self.upper):
            raise ValueError("rates must obey 0 < lower <= upper")


def _validate(n, rates):
    if n <= 0:
        raise ValueError("positive number of vertices required")
    for u, v, rate in rates:
        if not (isinstance(u, int) and isinstance(v, int)
                and 0 <= u < n and 0 <= v < n and rate > 0):
            raise ValueError("invalid vertex or nonpositive rate")


def multiplicative_potential(n, rates):
    """Return positive potentials p[v] >= rate * p[u], or None if impossible.

    Uses synchronous max-product Bellman-Ford from an implicit unit-weight
    super-source; exact Fraction arithmetic. Rates must be rational.
    """
    rates = tuple((u, v, Fraction(r)) for u, v, r in rates)
    _validate(n, rates)
    value = [Fraction(1) for _ in range(n)]
    for _ in range(n-1):
        after = value.copy()
        for u, v, rate in rates:
            after[v] = max(after[v], value[u] * rate)
        value = after
    if any(value[v] < value[u] * rate for u, v, rate in rates):
        return None
    return tuple(value)


def verify_potential(n, rates, potential):
    if potential is None or len(potential) != n or any(x <= 0 for x in potential):
        return False
    return all(potential[v] >= Fraction(r) * potential[u]
               for u, v, r in rates)


def profitable_cycle(n, rates):
    """Return a simple cycle as edge indices or None (exhaustive; small graphs).

    A returned certificate is checked independently by multiplying edge rates.
    The primary polynomial-time detector is multiplicative_potential.
    """
    rates = tuple((u, v, Fraction(r)) for u, v, r in rates)
    _validate(n, rates)
    outgoing = [[] for _ in range(n)]
    for i, (u, _, _) in enumerate(rates):
        outgoing[u].append(i)

    def search(start, current, used, edges, product):
        for i in outgoing[current]:
            _, dest, r = rates[i]
            if dest == start:
                if product * r > 1:
                    return edges + (i,)
            elif dest not in used and len(used) < n:
                witness = search(start, dest, used | {dest}, edges + (i,), product * r)
                if witness is not None:
                    return witness
        return None

    for start in range(n):
        witness = search(start, start, {start}, (), Fraction(1))
        if witness is not None:
            return witness
    return None


def certify_intervals(n, edges):
    """Three mutually exclusive sound labels for independent rate intervals.

    robust_no_cycle: upper-rate network has a feasible potential.
    guaranteed_cycle: lower-rate network has a specific profitable cycle.
    unresolved: neither certificate is available.
    """
    high = tuple((e.source, e.target, e.upper) for e in edges)
    low = tuple((e.source, e.target, e.lower) for e in edges)
    upper_potential = multiplicative_potential(n, high)
    if upper_potential is not None:
        return ('robust_no_cycle', upper_potential)
    lower_witness = profitable_cycle(n, low)
    if lower_witness is not None:
        return ('guaranteed_cycle', lower_witness)
    return ('unresolved', None)


def saturating_conversion(x, marginal_rate, curvature):
    """Example increasing concave f(x)=rx/(1+kx), with r>0 and k>=0."""
    x, r, k = Fraction(x), Fraction(marginal_rate), Fraction(curvature)
    if x < 0 or r <= 0 or k < 0:
        raise ValueError("need input >=0, marginal rate >0 and curvature >=0")
    return r*x/(1+k*x)


def cycle_conversion(x, edges):
    """Apply a finite sequence of (marginal_rate, curvature) conversions."""
    for r, k in edges:
        x = saturating_conversion(x, r, k)
    return x

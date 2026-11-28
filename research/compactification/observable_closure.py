"""NRF-04 exact rational gate-family rowspace closure and Jordan risk/leakage oracle.

The closure family permits all independent diagonal gates D. It is a
worst-case structural criterion when real activation gates are constrained.
"""
from __future__ import annotations
from fractions import Fraction as Q


def rref_basis(rows: tuple[tuple[Q, ...], ...], n: int) -> tuple[tuple[Q, ...], ...]:
    if n <= 0 or any(len(row) != n for row in rows):
        raise ValueError("invalid row shape")
    matrix = [[Q(x) for x in row] for row in rows]
    pivot = 0
    for col in range(n):
        choice = next((r for r in range(pivot, len(matrix)) if matrix[r][col]), None)
        if choice is None:
            continue
        matrix[pivot], matrix[choice] = matrix[choice], matrix[pivot]
        d = matrix[pivot][col]
        matrix[pivot] = [v / d for v in matrix[pivot]]
        for r in range(len(matrix)):
            if r == pivot:
                continue
            a = matrix[r][col]
            if a:
                matrix[r] = [x - a * y for x, y in zip(matrix[r], matrix[pivot])]
        pivot += 1
        if pivot == len(matrix):
            break
    return tuple(tuple(row) for row in matrix[:pivot])


def in_span(v: tuple[Q, ...], basis: tuple[tuple[Q, ...], ...]) -> bool:
    n = len(v)
    return len(rref_basis((*basis, tuple(v)), n)) == len(basis)


def robust_gate_closure(teacher: tuple[tuple[Q, ...], ...],
                        w1: tuple[tuple[Q, ...], ...],
                        w2: tuple[tuple[Q, ...], ...]):
    """Minimal rowspace containing C and invariant under every W2 E_j W1."""
    n = len(w2)
    if not teacher or n < 1 or not w1:
        raise ValueError("nonempty teacher and matrices required")
    p = len(w1)
    if any(len(row) != n for row in teacher) or any(len(row) != n for row in w1):
        raise ValueError("teacher/W1 dimensions disagree")
    if any(len(row) != p for row in w2):
        raise ValueError("W2 dimensions disagree")
    basis = rref_basis(teacher, n)
    ranks = [len(basis)]
    while True:
        new = [tuple(v) for v in basis]
        for j in range(p):
            active = any(sum((s[i] * w2[i][j] for i in range(n)), Q(0))
                         for s in basis)
            if active:
                new.append(tuple(w1[j]))
        candidate = rref_basis(tuple(new), n)
        if len(candidate) == len(basis):
            break
        basis = candidate
        ranks.append(len(basis))
        if len(basis) > n:
            raise AssertionError("rank exceeds ambient dimension")
    for j in range(p):
        if any(sum((s[i] * w2[i][j] for i in range(n)), Q(0))
               for s in basis):
            assert in_span(w1[j], basis)
    return {"rank": len(basis), "basis": basis, "rank_history": tuple(ranks)}


def jordan_frontier(u1: Q, u2: Q, coupling: Q):
    """Optimal isotropic task risk and squared leakage for P=u u^T."""
    if u1*u1 + u2*u2 != 1:
        raise ValueError("unit rational direction required")
    error = u2*u2
    leak_sq = coupling*coupling * (u1*u1)**2
    return error, leak_sq


def jordan_direct_leak_square(u1: Q, u2: Q, diagonal: Q, coupling: Q):
    """Independently evaluate ||P(aI+bE12)(I-P)||_F^2 over Q."""
    P = ((u1*u1, u1*u2), (u1*u2, u2*u2))
    IminusP = ((1-P[0][0], -P[0][1]), (-P[1][0], 1-P[1][1]))
    J = ((diagonal, coupling), (Q(0), diagonal))
    left = tuple(tuple(sum((P[i][k]*J[k][j] for k in range(2)), Q(0))
                       for j in range(2)) for i in range(2))
    mat = tuple(tuple(sum((left[i][k]*IminusP[k][j] for k in range(2)), Q(0))
                      for j in range(2)) for i in range(2))
    return sum((x*x for row in mat for x in row), Q(0))


def optimal_tradeoff_error(weight: Q, coupling: Q):
    """Minimize E + weight*b^2*(1-E)^2 on [0,1], in rational arithmetic."""
    if weight < 0:
        raise ValueError("nonnegative objective weight required")
    t = 2*weight*coupling*coupling
    return Q(0) if t <= 1 else 1-Q(1)/t


def tradeoff_cost(error: Q, weight: Q, coupling: Q):
    if not 0 <= error <= 1 or weight < 0:
        raise ValueError("error in [0,1] and nonnegative weight required")
    return error+weight*coupling*coupling*(1-error)**2

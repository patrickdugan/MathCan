"""NRF-08: exact-rational finite matrix oracle for suffix/dark transport."""
from __future__ import annotations
from fractions import Fraction as F

def matrix(rows):
    if not rows or any(len(row) != len(rows) for row in rows):
        raise ValueError("square matrix required")
    return tuple(tuple(F(x) for x in row) for row in rows)

def mmul(a, b):
    n = len(a)
    if len(b) != n or any(len(row) != n for row in (*a, *b)):
        raise ValueError("matching square matrices required")
    return tuple(tuple(sum((a[i][k]*b[k][j] for k in range(n)), F(0))
                       for j in range(n)) for i in range(n))

def add(a, b):
    return tuple(tuple(x + y for x, y in zip(ra, rb)) for ra, rb in zip(a, b))

def identity(n):
    return matrix([[int(i == j) for j in range(n)] for i in range(n)])

def difference(a, b):
    return tuple(tuple(x - y for x, y in zip(ra, rb)) for ra, rb in zip(a, b))

def rational_projector(t):
    t = F(t)
    u = ((1-t*t)/(1+t*t), 2*t/(1+t*t))
    return matrix([[u[i]*u[j] for j in range(2)] for i in range(2)])

def block_transport(P, S, J):
    """Exact P S J Q = (P S P)(P J Q) + (P S Q)(Q J Q)."""
    n = len(P)
    if len(S) != n or len(J) != n:
        raise ValueError("matching dimensions required")
    Q = difference(identity(n), P)
    old = mmul(mmul(P, J), Q)
    advected = mmul(mmul(P, mmul(S, P)), old)
    injection = mmul(mmul(P, mmul(S, Q)), mmul(Q, mmul(J, Q)))
    total = mmul(mmul(P, mmul(S, J)), Q)
    if add(advected, injection) != total:
        raise AssertionError("block identity failed")
    return old, advected, injection, total

def frobenius_squared(M):
    return sum((x*x for row in M for x in row), F(0))

def interference(A, B):
    return 2*sum((a*b for ar, br in zip(A, B) for a, b in zip(ar, br)), F(0))

def check_energy(A, B, T):
    return frobenius_squared(T) == (
        frobenius_squared(A) + frobenius_squared(B) + interference(A, B))

"""DEL-06: exact finite-dimensional Frobenius/Gysin shadow.

These rational matrices model:
  - Frobenius on a Gysin kernel and quotient (block upper triangular);
  - compatibility of high-degree Gysin isomorphisms by conjugacy;
  - point-count remainder sign and Tate (-1) twist;
  - diagonal tensor-power spectral occurrences.

No actual etale-cohomology groups are constructed in this module.
All computations use fractions.Fraction and Python's standard library.
"""
from fractions import Fraction as Q
from itertools import product
from math import prod


def mat(rows):
    return tuple(tuple(Q(x) for x in row) for row in rows)


def shape(A):
    if not A:
        return 0, 0
    m = len(A[0])
    if any(len(row) != m for row in A):
        raise ValueError("matrix has irregular rows")
    return len(A), m


def eye(n):
    return tuple(tuple(Q(i == j) for j in range(n)) for i in range(n))


def multiply(A, B):
    ra, ca = shape(A)
    rb, cb = shape(B)
    if ca != rb:
        raise ValueError("incompatible matrices")
    return tuple(tuple(sum((A[i][h] * B[h][j] for h in range(ca)), Q(0))
                       for j in range(cb)) for i in range(ra))


def power(A, n):
    rows, cols = shape(A)
    if rows != cols or n < 0:
        raise ValueError("nonnegative matrix powers require a square matrix")
    v = eye(rows)
    while n:
        if n & 1:
            v = multiply(v, A)
        n //= 2
        A = multiply(A, A)
    return v


def trace(A):
    r, c = shape(A)
    if r != c:
        raise ValueError("trace of a nonsquare matrix")
    return sum((A[i][i] for i in range(r)), Q(0))


def block_matrix(K, Qmat, cross, lower=None):
    a, a2 = shape(K)
    b, b2 = shape(Qmat)
    if a != a2 or b != b2:
        raise ValueError("block diagonal parts must be square")
    if shape(cross) != (a, b):
        raise ValueError("bad upper-right block")
    if lower is not None and shape(lower) != (b, a):
        raise ValueError("bad lower-left block")
    result = []
    for i in range(a):
        result.append(tuple(K[i]) + tuple(cross[i]))
    for i in range(b):
        bottom = tuple(lower[i]) if lower is not None else (Q(0),) * a
        result.append(bottom + tuple(Qmat[i]))
    return tuple(result)


def inverse(A):
    n, m = shape(A)
    if n != m:
        raise ValueError("non-square matrix")
    augmented = [list(A[i]) + list(eye(n)[i]) for i in range(n)]
    for i in range(n):
        pivot = next((j for j in range(i, n) if augmented[j][i]), None)
        if pivot is None:
            raise ValueError("singular change of basis")
        augmented[i], augmented[pivot] = augmented[pivot], augmented[i]
        factor = augmented[i][i]
        augmented[i] = [x / factor for x in augmented[i]]
        for j in range(n):
            if j == i:
                continue
            t = augmented[j][i]
            augmented[j] = [x - t * y
                            for x, y in zip(augmented[j], augmented[i])]
    return tuple(tuple(row[n:]) for row in augmented)


def conjugate(X, P):
    Pinv = inverse(P)
    return multiply(multiply(P, X), Pinv)


def powered_trace_splitting(K, Qmat, mix, n, lower=None):
    Y = block_matrix(K, Qmat, mix, lower)
    lhs = trace(power(Y, n))
    rhs = trace(power(K, n)) + trace(power(Qmat, n))
    return lhs, rhs


def signed_power_remainder(K, quotient, mix, lowest, high, n):
    """High pairs are (X, change-of-basis P); Y=P X P^-1."""
    Y = block_matrix(K, quotient, mix)
    main = trace(power(Y, n)) - trace(power(quotient, n))
    main += trace(power(lowest, n))
    for i, (X, P) in enumerate(high):
        Yhi = conjugate(X, P)
        main += (-1) ** (i + 1) * (
            trace(power(Yhi, n)) - trace(power(X, n)))
    return main


def tensor_spectrum(eigenvalues, k):
    if k < 0:
        raise ValueError("k must be nonnegative")
    return tuple(prod(indices, start=Q(1))
                 for indices in product(eigenvalues, repeat=k))


def tensor_power_trace(eigenvalues, k, n):
    spec = tensor_spectrum(tuple(map(Q, eigenvalues)), k)
    direct = sum((z ** n for z in spec), Q(0))
    expected = sum((Q(z) ** n for z in eigenvalues), Q(0)) ** k
    return direct, expected


def kunneth_lowest_degree_paths(d, k, max_degree=None):
    if not d >= 1 or k < 1:
        raise ValueError("d,k must be positive")
    D = d * k
    cap = D if max_degree is None else max_degree
    return tuple(xs for xs in product(range(cap + 1), repeat=k)
                 if sum(xs) == D and all(j >= d for j in xs))


def twist_trace_pair(r, eigens, n):
    if r <= 0 or n < 0:
        raise ValueError("r must be positive, n nonnegative")
    twisted = sum(((Q(r) * Q(lam)) ** n for lam in eigens), Q(0))
    expected = Q(r) ** n * sum((Q(lam) ** n for lam in eigens), Q(0))
    return twisted, expected

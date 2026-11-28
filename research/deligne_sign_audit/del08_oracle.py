"""DEL-08 exact finite-field oracle for fixed-coefficient hyperplanes.

The source's generic Bertini/Katz theorem is a geometric premise.
This module verifies finite-field algebraic consequences and mutants:
coefficient normalization, affine hyperbola discriminant, ambient
bipartite gradient certificate, finite-extension necessity, and the
failure of ambient smoothness to imply smoothness on an embedded curve.
All arithmetic is exact, including finite extension fields.
"""
from itertools import product
from research.deligne_sign_audit.prime_power_fourier import FIELDS


def affine_hyperplane(field, a, last, constant, fixed, z):
    out = field.add(field.mul(last, fixed), constant)
    for ai, zi in zip(a, z):
        out = field.add(out, field.mul(ai, zi))
    return out


def normalize_hyperplane(field, a, last, constant):
    if last == 0:
        raise ValueError("fixed-coordinate chart requires last coefficient nonzero")
    inv = field.inv(last)
    return tuple(field.mul(v, inv) for v in a), field.mul(constant, inv)


def check_normalized_zero_set(field, a, last, constant, fixed, z):
    anorm, cnorm = normalize_hyperplane(field, a, last, constant)
    lhs = affine_hyperplane(field, a, last, constant, fixed, z)
    rhs = affine_hyperplane(field, anorm, 1, cnorm, fixed, z)
    return lhs == field.mul(last, rhs), (lhs == 0) == (rhs == 0)


def conic(field, x, y, a, b, c):
    return field.add(
        field.add(field.mul(x, y), field.mul(a, x)),
        field.add(field.mul(b, y), c))


def conic_gradient(field, x, y, a, b):
    return field.add(y, a), field.add(x, b)


def conic_singular(field, a, b, c):
    x, y = field.neg(b), field.neg(a)
    gradient = conic_gradient(field, x, y, a, b)
    return conic(field, x, y, a, b, c) == 0, gradient


def conic_good(field, a, b, c):
    return c != field.mul(a, b)


def count_conic_good_parameters(field):
    q = field.q
    good = 0
    bad = 0
    for a, b, c in product(range(q), repeat=3):
        singular, gradient = conic_singular(field, a, b, c)
        if singular:
            bad += 1
            assert gradient == (0, 0)
            assert c == field.mul(a, b)
        else:
            good += 1
            assert c != field.mul(a, b)
    assert good == q * q * (q - 1) and bad == q * q
    return good, bad


def frobenius_gap(field):
    """x^p-x vanishes on F_p; nonzero at every non-prime-field
    element of the degree-two extension F_(p²)."""
    p = field.p
    outside = tuple(
        x for x in range(field.q)
        if field.sub(field.pow(x, p), x) != 0)
    base_zero = all(field.sub(field.pow(x, p), x) == 0
                    for x in range(p))
    return base_zero, len(outside), outside


def bipartite_quadratic(field, A, x, y):
    out = 0
    for i, xi in enumerate(x):
        derivative = 0
        for j, yj in enumerate(y):
            derivative = field.add(derivative,
                                  field.mul(A[i][j], yj))
        out = field.add(out, field.mul(xi, derivative))
    return out


def bipartite_partial_x(field, A, y):
    return tuple(
        sum_field(field, (field.mul(A[i][j], y[j])
                          for j in range(len(y))))
        for i in range(len(A)))


def sum_field(field, items):
    z = 0
    for a in items:
        z = field.add(z, a)
    return z


def check_bipartite_level(field, A, x, y, c):
    if c == 0:
        raise ValueError("nonzero level is essential")
    Q = bipartite_quadratic(field, A, x, y)
    partials = bipartite_partial_x(field, A, y)
    euler = sum_field(field, (field.mul(u, du)
                              for u, du in zip(x, partials)))
    assert Q == euler
    return field.add(Q, c) != 0 or any(t != 0 for t in partials)


def tangent_line_restriction_mutant(field):
    """Smooth ambient hyperbola xy+1=0, line y=x-2 tangent at
    (1,-1), whose restricted equation is (x-1)^2."""
    one = 1
    minus_one = field.neg(one)
    y = field.sub(one, 2 % field.p)
    assert y == minus_one
    ambient = conic(field, one, minus_one, 0, 0, one)
    gx, gy = conic_gradient(field, one, minus_one, 0, 0)
    restricted = field.add(field.mul(one, y), one)
    # derivative of x(x-2)+1 is 2*(x-1), zero at x=1
    tangent_derivative = field.add(gx, gy)
    return ambient == 0 and restricted == 0, (
        gx != 0 or gy != 0), tangent_derivative == 0


def graph_nonimmersion_collision(field):
    """Coordinates (x,xy) fail to separate (0,0),(0,1)."""
    a, b = (0,0),(0,1)
    def image(x,y):
        return x, field.mul(x,y)
    return a != b, image(*a) == image(*b)

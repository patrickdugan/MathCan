"""Exact Gram witness for three rank-one projectors with distinct holonomy.

The construction proves a loss of information when retaining only pairwise
projector overlaps. Full projectors recover the missing triple invariant.
"""
from fractions import Fraction as F


def triangle_gram(orientation):
    """Two positive-definite Gram matrices with |g_ij| = 1/4 off diagonal."""
    if orientation not in (-1, 1):
        raise ValueError("orientation must be +1 or -1")
    a = F(1, 4)
    return ((F(1), a, orientation*a),
            (a, F(1), a),
            (orientation*a, a, F(1)))


def determinant3(m):
    a, b, c = m[0]
    d, e, f = m[1]
    g, h, i = m[2]
    return a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)


def positive_definite3(m):
    """Sylvester's criterion for symmetric 3x3 matrices."""
    if any(m[i][j] != m[j][i] for i in range(3) for j in range(3)):
        return False
    return m[0][0] > 0 and m[0][0]*m[1][1]-m[0][1]*m[1][0] > 0 and determinant3(m) > 0


def pairwise_projector_overlaps(m):
    """tr(P_i P_j) = <u_i,u_j>^2 for unit vectors u_i."""
    return (m[0][1]**2, m[1][2]**2, m[2][0]**2)


def triple_projector_trace(m):
    """tr(P0 P1 P2) = <u0,u1><u1,u2><u2,u0>."""
    return m[0][1]*m[1][2]*m[2][0]


def rank_one_loop_sign(m):
    """Polar-sign holonomy, defined only for nonzero pairwise overlaps."""
    t = triple_projector_trace(m)
    if t == 0:
        raise ValueError("one overlap vanished; polar sign is undefined")
    return 1 if t > 0 else -1


def gauge_flip(m, signs):
    if len(signs) != 3 or any(s not in (-1, 1) for s in signs):
        raise ValueError("one sign per vertex required")
    return tuple(tuple(signs[i]*m[i][j]*signs[j] for j in range(3))
                 for i in range(3))


def multiply2(a, b):
    return tuple(tuple(sum((a[i][k]*b[k][j] for k in range(2)), F(0))
                       for j in range(2)) for i in range(2))


def transpose2(m):
    return tuple(tuple(m[j][i] for j in range(2)) for i in range(2))


def rotation(a, b):
    a, b = F(a), F(b)
    if a*a+b*b != 1:
        raise ValueError("rotation must be exactly orthogonal")
    return ((a, -b), (b, a))


def matrix_loop(edges):
    ident = ((F(1), F(0)), (F(0), F(1)))
    result = ident
    for m in edges:
        result = multiply2(result, m)
    return result


def gauge_transport(m, q_src, q_dst):
    return multiply2(multiply2(transpose2(q_src), m), q_dst)

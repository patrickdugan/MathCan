"""DEL-22E: independent Schur numerator checks over finite fields and sparse polynomials.

The determinant of a bordered pivot H must equal
    det(H)*v - c*adj(H)*b
as a polynomial, including when det(H)=0, in characteristic 2,
and for the original DEL-16 nonreduced/redundant equations.
The Lean chart theorem requires det(H) to be a unit; this independent
oracle also checks the broader polynomial identity numerically.
"""
from __future__ import annotations

from itertools import combinations
from random import Random
import unittest

from tests.test_deligne21g_geometric_fiber import (
    cases, elements, fields, original_jacobian, rank
)
from tests.test_deligne21h_field_towers import F4_ZERO, embed
from tests.test_deligne22a_relative_critical import determinant
from tests.test_deligne22b_universal_section import (
    universal_section, universal_original_rows, determinant_poly,
    formal_partial, monomial, add_poly, neg_poly, mul_poly
)
from tests.test_deligne22c_rankd_pivot import adjugate, det0


def numerical_block_det(h, b, c, v):
    return determinant([list(row) + [b[i]] for i, row in enumerate(h)] +
                       [list(c) + [v]])


def numerical_numerator(h, b, c, v, one):
    n = len(h)
    adj = adjugate(h, one)
    correction = sum((c[i] * adj[i][j] * b[j]
                      for i in range(n) for j in range(n)), one.elt(0))
    return det0(h, one) * v - correction


def symbolic_det(square, n):
    return monomial(n, {}) if not square else determinant_poly(square)


def symbolic_adj(square, n):
    d = len(square)
    return [
        [
            (neg_poly if (i + j) % 2 else lambda x: x)(
                symbolic_det([[x for q, x in enumerate(row) if q != i]
                              for p, row in enumerate(square) if p != j], n)
            ) for j in range(d)
        ] for i in range(d)
    ]


def symbolic_numerator(h, b, c, v, n):
    d = len(h)
    det = symbolic_det(h, n)
    adj = symbolic_adj(h, n)
    correction = [
        mul_poly(mul_poly(c[i], adj[i][j]), b[j])
        for i in range(d) for j in range(d)
    ]
    return add_poly(mul_poly(det, v), *(neg_poly(term) for term in correction))


def symbolic_block_det(h, b, c, v, n):
    return determinant_poly(
        [list(row) + [b[i]] for i, row in enumerate(h)]
        + [list(c) + [v]]
    )


class SchurNumeratorOracle(unittest.TestCase):
    def test_field_invertible_and_singular_blocks(self):
        rng = Random(22023)
        for p, z, one, _ in fields():
            ff = elements(z)
            for d in range(5):
                for mode in ("random", "singular"):
                    for _ in range(30):
                        h = [[rng.choice(ff) for _ in range(d)] for _ in range(d)]
                        if mode == "singular" and d >= 2:
                            h[-1] = list(h[0])
                        b = [rng.choice(ff) for _ in range(d)]
                        c = [rng.choice(ff) for _ in range(d)]
                        v = rng.choice(ff)
                        self.assertEqual(
                            numerical_block_det(h, b, c, v),
                            numerical_numerator(h, b, c, v, one),
                            (p, d, mode, h, b, c, v)
                        )

    def test_gf4_gf16_base_change(self):
        z, one = F4_ZERO, F4_ZERO.elt(1)
        alpha = z.elt(0, 1)
        h = [[one, alpha], [alpha + one, z]]
        b, c, v = [alpha, one], [one, alpha + one], alpha
        d4 = numerical_numerator(h, b, c, v, one)
        h16 = [[embed(x) for x in row] for row in h]
        b16 = [embed(x) for x in b]
        c16 = [embed(x) for x in c]
        v16 = embed(v)
        self.assertEqual(
            embed(d4),
            numerical_numerator(h16, b16, c16, v16, embed(one))
        )

    def test_symbolic_original_ideal_polynomial_identity(self):
        for p, z, one, alpha in fields():
            for mode, point in cases(z, one, alpha):
                n = len(point)
                polynomial_rows = universal_original_rows(mode, n)
                gradient = [formal_partial(universal_section(n), j)
                            for j in range(n)]
                numeric_rows = original_jacobian(mode, *point)
                d = rank(numeric_rows)
                if d > len(polynomial_rows):
                    raise AssertionError("invalid fixture rank")
                for selected_rows in combinations(range(len(polynomial_rows)), d):
                    for columns in combinations(range(n), d):
                        h = [[polynomial_rows[t][j] for j in columns]
                             for t in selected_rows]
                        c = [gradient[j] for j in columns]
                        for j in range(n):
                            b = [polynomial_rows[t][j] for t in selected_rows]
                            v = gradient[j]
                            self.assertEqual(
                                symbolic_block_det(h, b, c, v, n),
                                symbolic_numerator(h, b, c, v, n),
                                (p, mode, selected_rows, columns, j)
                            )


if __name__ == "__main__":
    unittest.main()

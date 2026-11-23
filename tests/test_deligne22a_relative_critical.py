"""DEL-22A independent exact original-ideal critical/Jacobian-rank oracle.

For each actual DEL-16-style test presentation, the pulled-back section
has an original-polynomial gradient. Verify conormal membership, zero
derivative on every Jacobian tangent, augmented rank, Lagrange
multipliers, and vanishing of the expected maximal minors. The Lean
theorems prove the rank equivalence for arbitrary geometric field points.
"""
from __future__ import annotations

from itertools import combinations, product
import unittest

from tests.test_deligne21g_geometric_fiber import (
    cases, dot, elements, fields, original_jacobian, rank, scheme_equations
)
from tests.test_deligne21h_field_towers import (
    F4_ZERO, embed, original_jacobian as original_jacobian16
)


def derivative_of_section(u, a):
    """Use B=x*y for one factor and B=x_1*x_2 for two parabolas."""
    if len(u) == 2:
        return (u[1] + a[0], u[0] + a[1])
    assert len(u) == 4
    z = u[0].elt(0)
    return (u[2] + a[0], z + a[1], u[0] + a[2], z + a[3])


def value_of_section(u, a, c):
    b = u[0] * (u[1] if len(u) == 2 else u[2])
    return b + sum((a[i] * u[i] for i in range(len(u))), c)


def linear_span_contains(rows, vector, field):
    z = field[0]
    return any(
        tuple(sum((lam[t] * rows[t][i] for t in range(len(rows))), z)
              for i in range(len(vector))) == tuple(vector)
        for lam in product(field, repeat=len(rows))
    )


def determinant(square):
    n = len(square)
    if n == 0:
        raise AssertionError("Use nonempty minors")
    if n == 1:
        return square[0][0]
    z = square[0][0].elt(0)
    ans = z
    for j, x in enumerate(square[0]):
        sub = [row[:j] + row[j+1:] for row in square[1:]]
        term = x * determinant(sub)
        ans = ans - term if j % 2 else ans + term
    return ans


def all_minors_zero(rows, size):
    if size > len(rows) or size > len(rows[0]):
        return True
    z = rows[0][0].elt(0)
    for rs in combinations(range(len(rows)), size):
        for cols in combinations(range(len(rows[0])), size):
            minor = [[rows[r][c] for c in cols] for r in rs]
            if determinant(minor) != z:
                return False
    return True


class Deligne22ARelativeCriticalOracle(unittest.TestCase):
    def test_geometric_criticality_augmented_rank_and_maximal_minors(self):
        for p, zero, one, alpha in fields():
            field = elements(zero)
            for mode, u in cases(zero, one, alpha):
                n = len(u)
                self.assertTrue(all(
                    v == zero for v in scheme_equations(mode, *u)
                ), (p, mode))
                rows = original_jacobian(mode, *u)
                d = rank(rows)
                tangents = tuple(
                    v for v in product(field, repeat=n)
                    if all(dot(row, v) == zero for row in rows)
                )
                self.assertEqual(len(tangents), p ** (2 * (n-d)))
                scalars = tuple(zero.elt(i) for i in range(p))
                choices = [
                    tuple(scalars[(i+j) % p] for i in range(n))
                    for j in range(min(p, 3))
                ]
                choices += [tuple(one if i == 0 else zero for i in range(n))]
                for a in choices:
                    g = derivative_of_section(u, a)
                    augmented = rows + [list(g)]
                    by_tangent = all(dot(g, v) == zero for v in tangents)
                    by_lagrange = linear_span_contains(rows, g, field)
                    by_rank = rank(augmented) == d
                    by_minors = all_minors_zero(augmented, d + 1)
                    self.assertEqual(
                        (by_tangent, by_lagrange, by_rank, by_minors),
                        (by_rank,) * 4, (p, mode, a, g)
                    )
                    for c in (zero, one):
                        is_section_zero = value_of_section(u, a, c) == zero
                        self.assertEqual(
                            is_section_zero and by_tangent,
                            is_section_zero and by_minors,
                            (p, mode, a, c)
                        )

    def test_nonreduced_x_squared_vs_radical_x_in_char_two(self):
        zero, one = F4_ZERO, F4_ZERO.elt(1)
        u = (zero, zero)
        grad = (one, zero)
        thick = original_jacobian("double_line", *u)
        radical = original_jacobian("radical_line", *u)
        self.assertEqual((rank(thick), rank(radical)), (0, 1))
        self.assertEqual((rank(thick + [list(grad)]),
                          rank(radical + [list(grad)])), (1, 1))
        self.assertFalse(linear_span_contains(thick, grad, elements(zero)))
        self.assertTrue(linear_span_contains(radical, grad, elements(zero)))

    def test_gf4_to_gf16_preserves_rank_criticality_and_original_rows(self):
        zero, one = F4_ZERO, F4_ZERO.elt(1)
        a = (one, zero)
        for mode, u in cases(zero, one, one):
            rows = original_jacobian(mode, *u)
            grad = derivative_of_section(u, a if len(u) == 2 else (one, zero, zero, zero))
            u16 = tuple(map(embed, u))
            rows16 = original_jacobian16(mode, *u16)
            grad16 = tuple(map(embed, grad))
            self.assertEqual(rows16, [[embed(x) for x in row] for row in rows])
            self.assertEqual(rank(rows), rank(rows16))
            self.assertEqual(
                rank(rows + [list(grad)]) == rank(rows),
                rank(rows16 + [list(grad16)]) == rank(rows16),
                mode,
            )


if __name__ == "__main__":
    unittest.main()

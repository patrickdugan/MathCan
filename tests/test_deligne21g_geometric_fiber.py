"""DEL-21G independent geometric-point oracle over GF(4) and GF(9).

These arithmetic tests exercise points outside the coefficient field,
with original (not radicalized) polynomial ideals, Jacobian rows,
quotient pairings and Frobenius compatibility. The actual Kähler-fiber
equivalence is proved separately by pinned Lean.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
import unittest


@dataclass(frozen=True)
class Fp2:
    a: int
    b: int
    p: int
    q1: int
    q0: int

    def __post_init__(self):
        object.__setattr__(self, "a", self.a % self.p)
        object.__setattr__(self, "b", self.b % self.p)

    def elt(self, a: int, b: int = 0) -> "Fp2":
        return Fp2(a, b, self.p, self.q1, self.q0)

    def __add__(self, other: "Fp2") -> "Fp2":
        return self.elt(self.a + other.a, self.b + other.b)

    def __neg__(self) -> "Fp2":
        return self.elt(-self.a, -self.b)

    def __sub__(self, other: "Fp2") -> "Fp2":
        return self + (-other)

    def __mul__(self, other: "Fp2") -> "Fp2":
        # alpha**2 = -q1*alpha - q0, where x**2+q1*x+q0 is irreducible.
        return self.elt(
            self.a * other.a - self.q0 * self.b * other.b,
            self.a * other.b + self.b * other.a - self.q1 * self.b * other.b,
        )

    def __rmul__(self, other: int) -> "Fp2":
        if not isinstance(other, int):
            return NotImplemented
        return self.elt(other) * self

    def __pow__(self, exponent: int) -> "Fp2":
        if exponent < 0:
            return self.inv() ** (-exponent)
        result, base = self.elt(1), self
        while exponent:
            if exponent & 1:
                result = result * base
            base = base * base
            exponent //= 2
        return result

    def inv(self) -> "Fp2":
        if self == self.elt(0):
            raise ZeroDivisionError("zero is not invertible")
        return self ** (self.p * self.p - 2)

    def __truediv__(self, other: "Fp2") -> "Fp2":
        return self * other.inv()


def fields():
    # x^2+x+1 over F2, x^2+1 over F3; both irreducible.
    for p, q1, q0 in ((2, 1, 1), (3, 0, 1)):
        zero = Fp2(0, 0, p, q1, q0)
        yield p, zero, zero.elt(1), zero.elt(0, 1)


def elements(zero: Fp2):
    return [zero.elt(a, b) for a in range(zero.p) for b in range(zero.p)]


def scheme_equations(mode: str, x, y, x2=None, y2=None):
    if mode == "parabola":
        return [y - x * x]
    if mode in ("node_origin", "node_smooth"):
        return [x * y]
    if mode == "double_line":
        return [x * x]
    if mode == "radical_line":
        return [x]
    if mode == "redundant":
        return [x * x, x * x * x]
    if mode == "product_parabolas":
        return [y - x * x, y2 - x2 * x2]
    raise AssertionError(mode)


def original_jacobian(mode: str, x, y, x2=None, y2=None):
    z, one = x.elt(0), x.elt(1)
    if mode == "parabola":
        return [[-2 * x, one]]
    if mode in ("node_origin", "node_smooth"):
        return [[y, x]]
    if mode == "double_line":
        return [[2 * x, z]]
    if mode == "radical_line":
        return [[one, z]]
    if mode == "redundant":
        return [[2 * x, z], [3 * x * x, z]]
    if mode == "product_parabolas":
        return [[-2 * x, one, z, z], [z, z, -2 * x2, one]]
    raise AssertionError(mode)


def rank(rows):
    if not rows:
        return 0
    zero = rows[0][0].elt(0)
    mat = [list(row) for row in rows]
    rr = 0
    for c in range(len(mat[0])):
        pivot = next((i for i in range(rr, len(mat)) if mat[i][c] != zero), None)
        if pivot is None:
            continue
        mat[rr], mat[pivot] = mat[pivot], mat[rr]
        inverse = mat[rr][c].inv()
        mat[rr] = [inverse * a for a in mat[rr]]
        for i in range(len(mat)):
            if i != rr:
                coeff = mat[i][c]
                mat[i] = [a - coeff * b for a, b in zip(mat[i], mat[rr])]
        rr += 1
    return rr


def dot(v, w):
    z = v[0].elt(0)
    for a, b in zip(v, w):
        z = z + a * b
    return z


def row_span(rows, zero):
    if not rows:
        return {()}
    field = elements(zero)
    width = len(rows[0])
    answer = set()
    for lam in product(field, repeat=len(rows)):
        answer.add(tuple(
            sum((lam[j] * rows[j][i] for j in range(len(rows))), zero)
            for i in range(width)
        ))
    return answer


def cases(zero, one, alpha):
    beta = alpha + one
    return [
        ("parabola", (alpha, alpha ** 2)),
        ("node_origin", (zero, zero)),
        ("node_smooth", (alpha, zero)),
        ("double_line", (zero, alpha)),
        ("radical_line", (zero, alpha)),
        ("redundant", (zero, alpha)),
        ("product_parabolas", (alpha, alpha ** 2, beta, beta ** 2)),
    ]


class GeometricFiberOracle(unittest.TestCase):
    def test_fields_are_genuine_quadratic_extensions(self):
        for p, z, one, alpha in fields():
            ff = elements(z)
            self.assertEqual(len(set(ff)), p * p)
            self.assertNotIn(alpha, [z.elt(a) for a in range(p)])
            self.assertEqual(len({a * b for a in ff for b in ff}), p * p)
            self.assertTrue(all(a * a.inv() == one for a in ff if a != z))

    def test_geometric_points_satisfy_original_full_ideal_generators(self):
        for p, z, one, alpha in fields():
            for mode, coords in cases(z, one, alpha):
                self.assertTrue(all(v == z for v in scheme_equations(mode, *coords)),
                                (p, mode, coords))

    def test_geometric_jacobian_rank_and_cotangent_dimensions(self):
        for p, z, one, alpha in fields():
            q = p * p
            for mode, coords in cases(z, one, alpha):
                rows = original_jacobian(mode, *coords)
                rel_rank = rank(rows)
                self.assertEqual(len(row_span(rows, z)), q ** rel_rank)
                n = len(rows[0])
                self.assertEqual(q ** (n - rel_rank) * q ** rel_rank, q ** n)
                # Count annihilating vectors, including extension-field coordinates.
                tangents = sum(
                    all(dot(row, v) == z for row in rows)
                    for v in product(elements(z), repeat=n)
                )
                self.assertEqual(tangents, q ** (n - rel_rank), (p, mode))

    def test_pairing_descends_to_actual_geometric_cotangent_quotient(self):
        for p, z, one, alpha in fields():
            ff = elements(z)
            for mode, coords in cases(z, one, alpha):
                if mode == "product_parabolas":
                    continue
                rows = original_jacobian(mode, *coords)
                relation_span = row_span(rows, z)
                n = len(rows[0])
                for v in product(ff, repeat=n):
                    if any(dot(row, v) != z for row in rows):
                        continue
                    for x in product(ff, repeat=n):
                        for rel in relation_span:
                            self.assertEqual(
                                dot(v, x), dot(v, tuple(a + b for a, b in zip(x, rel)))
                            )

    def test_nonreduced_radical_mutant(self):
        for p, z, one, alpha in fields():
            thick = original_jacobian("double_line", z, alpha)
            radical = original_jacobian("radical_line", z, alpha)
            self.assertEqual(rank(thick), 0)
            self.assertEqual(rank(radical), 1)
            self.assertNotEqual(row_span(thick, z), row_span(radical, z))
            self.assertEqual(dot(thick[0], (one, z)), z)
            self.assertNotEqual(dot(radical[0], (one, z)), z)

    def test_redundant_equations_and_product_factor_independence(self):
        for p, z, one, alpha in fields():
            self.assertEqual(
                row_span(original_jacobian("redundant", z, alpha), z),
                row_span(original_jacobian("double_line", z, alpha), z),
            )
            beta = alpha + one
            j = original_jacobian("product_parabolas",
                                  alpha, alpha ** 2, beta, beta ** 2)
            self.assertEqual(j[0][2:], [z, z])
            self.assertEqual(j[1][:2], [z, z])
            self.assertEqual(rank(j), 2)

    def test_prime_field_frobenius_naturality_on_geometric_points(self):
        # The Frobenius automorphism fixes base-field coefficients and
        # commutes with polynomial evaluation and formal partial derivatives.
        for p, z, one, alpha in fields():
            for mode, coords in cases(z, one, alpha):
                images = tuple(t ** p for t in coords)
                self.assertEqual(
                    [v ** p for v in scheme_equations(mode, *coords)],
                    scheme_equations(mode, *images),
                )
                self.assertEqual(
                    [[v ** p for v in row] for row in original_jacobian(mode, *coords)],
                    original_jacobian(mode, *images),
                )


if __name__ == "__main__":
    unittest.main()

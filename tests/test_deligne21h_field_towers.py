"""DEL-21H field-tower oracle: GF(2) ⊂ GF(4) ⊂ GF(16).

Checks the *actual* lifted equation gradients and the coordinate quotient
transport under an explicit field embedding. Lean proves the categorical
Kähler-fiber naturality separately; these arithmetic tests are independent
and retain nilpotent and redundant polynomial equations.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
import unittest

from tests.test_deligne21g_geometric_fiber import (
    Fp2, cases, original_jacobian, rank, scheme_equations,
)


@dataclass(frozen=True)
class GF16:
    bits: int

    def __post_init__(self):
        object.__setattr__(self, "bits", self.bits & 15)

    def elt(self, a: int, b: int = 0) -> "GF16":
        # Only constants are needed for the generic polynomial-oracle helpers.
        assert b == 0
        return GF16(a & 1)

    def __add__(self, other: "GF16") -> "GF16":
        return GF16(self.bits ^ other.bits)

    def __sub__(self, other: "GF16") -> "GF16":
        return self + other

    def __neg__(self) -> "GF16":
        return self

    def __mul__(self, other: "GF16") -> "GF16":
        # GF(16)=GF(2)[theta]/(theta^4+theta+1).
        a, b, out = self.bits, other.bits, 0
        while b:
            if b & 1:
                out ^= a
            b >>= 1
            a <<= 1
            if a & 16:
                a ^= 0b10011
        return GF16(out)

    def __rmul__(self, n: int) -> "GF16":
        if not isinstance(n, int):
            return NotImplemented
        return GF16(n & 1) * self

    def __pow__(self, n: int) -> "GF16":
        if n < 0:
            return self.inv() ** (-n)
        out, base = GF16(1), self
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n >>= 1
        return out

    def inv(self) -> "GF16":
        if self.bits == 0:
            raise ZeroDivisionError
        return self ** 14

    def __truediv__(self, other: "GF16") -> "GF16":
        return self * other.inv()


F4_ZERO = Fp2(0, 0, 2, 1, 1)
F4 = [F4_ZERO.elt(a, b) for a, b in product(range(2), repeat=2)]
F16 = [GF16(a) for a in range(16)]
THETA = GF16(2)
BETA = THETA ** 5  # order-3 root of X^2+X+1 inside GF(16)


def embed(x: Fp2) -> GF16:
    assert x.p == 2 and x.q1 == 1 and x.q0 == 1
    return GF16(x.a) + GF16(x.b) * BETA


def field_cases():
    alpha = F4_ZERO.elt(0, 1)
    return cases(F4_ZERO, F4_ZERO.elt(1), alpha)


def row_span(field, rows):
    zero = field[0]
    n = len(rows[0])
    return {
        tuple(
            sum((coefs[t] * rows[t][i] for t in range(len(rows))), zero)
            for i in range(n)
        )
        for coefs in product(field, repeat=len(rows))
    }


def dot(u, v):
    zero = u[0].elt(0)
    return sum((a * b for a, b in zip(u, v)), zero)


def row_basis_mod_relations(rows, zero):
    """Select coordinate representatives independent modulo row span."""
    n = len(rows[0])
    one = zero.elt(1)
    chosen = []
    for j in range(n):
        unit = [one if i == j else zero for i in range(n)]
        if rank(rows + chosen + [unit]) > rank(rows + chosen):
            chosen.append(unit)
    return chosen


class Deligne21HFieldTowerOracle(unittest.TestCase):
    def test_actual_quadratic_embedding_is_a_field_homomorphism(self):
        self.assertEqual(BETA * BETA + BETA + GF16(1), GF16(0))
        self.assertNotIn(BETA, (GF16(0), GF16(1)))
        self.assertEqual(len(set(F16)), 16)
        self.assertEqual(len(set(F4)), 4)
        self.assertEqual(len(set(embed(x) for x in F4)), 4)
        for x, y in product(F4, repeat=2):
            self.assertEqual(embed(x + y), embed(x) + embed(y))
            self.assertEqual(embed(x * y), embed(x) * embed(y))
        self.assertTrue(all(x * x.inv() == GF16(1) for x in F16[1:]))

    def test_on_scheme_points_and_full_original_jacobian_commute(self):
        for mode, u in field_cases():
            l_rows = original_jacobian(mode, *u)
            m_u = tuple(map(embed, u))
            m_rows = original_jacobian(mode, *m_u)
            self.assertTrue(all(z == F4_ZERO for z in scheme_equations(mode, *u)))
            self.assertTrue(all(z == GF16(0) for z in scheme_equations(mode, *m_u)))
            self.assertEqual([[embed(x) for x in row] for row in l_rows, m_rows)
            self.assertEqual(rank(l_rows), rank(m_rows), mode)

    def test_relations_and_tensor_quotient_basis_extend_correctly(self):
        for mode, u in field_cases():
            l_rows = original_jacobian(mode, *u)
            m_rows = original_jacobian(mode, *tuple(map(embed, u)))
            r = rank(l_rows)
            n = len(l_rows[0])
            self.assertEqual(len(row_span(F4, l_rows)), 4 ** r, mode)
            self.assertEqual(len(row_span(F16, m_rows)), 16 ** r, mode)
            quotient_reps = row_basis_mod_relations(l_rows, F4_ZERO)
            self.assertEqual(len(quotient_reps), n - r, mode)
            mapped_reps = [[embed(x) for x in v] for v in quotient_reps]
            self.assertEqual(rank(m_rows + mapped_reps), n, mode)

    def test_quotient_representative_transport_independence(self):
        for mode, u in field_cases():
            l_rows = original_jacobian(mode, *u)
            m_rows = original_jacobian(mode, *tuple(map(embed, u)))
            rel_l = row_span(F4, l_rows)
            rel_m = row_span(F16, m_rows)
            n = len(l_rows[0])
            vectors = list(product(F4, repeat=n))
            if n > 2:
                vectors = vectors[::max(1, len(vectors) // 8)]
            for vector in vectors:
                for rel in rel_l:
                    moved = tuple(a + b for a, b in zip(vector, rel))
                    for scalar in F16:
                        image = lambda v: tuple(scalar * embed(x) for x in v)
                        delta = tuple(a - b for a, b in zip(image(moved), image(vector)))
                        self.assertIn(delta, rel_m, (mode, vector, rel, scalar))

    def test_tangent_annihilator_and_dual_pairing_naturality(self):
        for mode, u in field_cases():
            l_rows = original_jacobian(mode, *u)
            m_rows = original_jacobian(mode, *tuple(map(embed, u)))
            n = len(l_rows[0])
            for v in product(F4, repeat=n):
                phi_v = tuple(map(embed, v))
                for row_l, row_m in zip(l_rows, m_rows):
                    self.assertEqual(embed(dot(row_l, v)), dot(row_m, phi_v))
                if all(dot(row, v) == F4_ZERO for row in l_rows):
                    for scalar in (GF16(0), GF16(1), GF16(5), GF16(15)):
                        tangent_m = tuple(scalar * x for x in phi_v)
                        self.assertTrue(all(dot(row, tangent_m) == GF16(0) for row in m_rows))

    def test_nonreduced_vs_radical_mutant_is_not_collapsed(self):
        z, a = F4_ZERO, F4_ZERO.elt(0, 1)
        for zero, x in ((z, a), (GF16(0), embed(a))):
            thick = original_jacobian("double_line", zero, x)
            radical = original_jacobian("radical_line", zero, x)
            self.assertEqual(rank(thick), 0)
            self.assertEqual(rank(radical), 1)


if __name__ == "__main__":
    unittest.main()

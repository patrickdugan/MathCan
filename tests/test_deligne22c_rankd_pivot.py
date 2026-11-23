"""DEL-22C exact rank-d pivot and Schur-complement oracle.

Cross-check the arbitrary-rank local criticality calculation over GF(4)
and GF(9), including rank-drop mutants. Independent of Lean proofs.
"""
from __future__ import annotations

from itertools import combinations
import random
import unittest

from tests.test_deligne21g_geometric_fiber import fields, elements, rank
from tests.test_deligne22a_relative_critical import determinant, all_minors_zero


def det0(square, one):
    """The determinant of an empty 0x0 matrix is one."""
    return one if not square else determinant(square)


def adjugate(matrix, one):
    """Explicit cofactor-transpose formula over any field."""
    d = len(matrix)
    return [[(one.elt(-1) if (i + j) % 2 else one) *
             det0([row[:i] + row[i+1:]
                   for k, row in enumerate(matrix) if k != j], one)
             for j in range(d)] for i in range(d)]


def pivot_minor_values(rows, g, rs, cs, one):
    """Delta*g_j - g_C*adj(H)*J_(R,j), with H=J_(R,C)."""
    h = [[rows[i][j] for j in cs] for i in rs]
    delta = det0(h, one)
    adj = adjugate(h, one)
    g_c = [g[j] for j in cs]
    q = []
    for j in range(len(g)):
        correction = sum((g_c[a] * adj[a][b] * rows[rs[b]][j]
                          for a in range(len(cs)) for b in range(len(cs))),
                         one.elt(0))
        q.append(delta * g[j] - correction)
    return delta, q


class RankDPivotOracle(unittest.TestCase):
    def test_rank_zero_to_three_chart_equivalence_and_block_determinants(self):
        randomizer = random.Random(22023)
        for p, zero, one, _alpha in fields():
            ff = elements(zero)
            for d in range(4):
                width = d + 2
                for trial in range(40):
                    if d:
                        for _ in range(100):
                            h = [[randomizer.choice(ff) for _ in range(d)]
                                 for _ in range(d)]
                            if determinant(h) != zero:
                                break
                        else:
                            raise AssertionError("could not sample invertible pivot")
                        basis = [h[i] + [randomizer.choice(ff)
                                         for _ in range(width-d)] for i in range(d)]
                        multipliers = [randomizer.choice(ff) for _ in range(d)]
                        redundant = [sum((multipliers[i] * basis[i][j]
                                          for i in range(d)), zero)
                                     for j in range(width)]
                        rows = basis + [redundant]
                    else:
                        rows = [[zero for _ in range(width)]]
                    permutation = list(range(width))
                    randomizer.shuffle(permutation)
                    rows = [[r[i] for i in permutation] for r in rows]
                    cs = [permutation.index(i) for i in range(d)]
                    rs = list(range(d))
                    self.assertEqual(rank(rows), d)
                    delta = det0([[rows[i][j] for j in cs] for i in rs], one)
                    self.assertNotEqual(delta, zero)
                    for in_span in (True, False):
                        if in_span:
                            mu = [randomizer.choice(ff) for _ in range(d)]
                            g = [sum((mu[i] * rows[i][j] for i in rs), zero)
                                 for j in range(width)]
                        else:
                            g = [randomizer.choice(ff) for _ in range(width)]
                        pivot, qs = pivot_minor_values(rows, g, rs, cs, one)
                        self.assertEqual(pivot, delta)
                        self.assertTrue(all(qs[j] == zero for j in cs))
                        for j in range(width):
                            block = [[rows[i][c] for c in cs] + [rows[i][j]]
                                     for i in rs]
                            block.append([g[c] for c in cs] + [g[j]])
                            self.assertEqual(qs[j], determinant(block),
                                             (p, d, trial, j))
                        criterion = rank(rows + [g]) == d
                        self.assertEqual(all(q == zero for q in qs), criterion)
                        self.assertEqual(all_minors_zero(rows + [g], d + 1),
                                         criterion)

    def test_char_two_nonreduced_rank_drop_mutant(self):
        p, zero, one, _ = next(fields())
        self.assertEqual(p, 2)
        # x^2=0 has zero formal derivative in char 2.
        jacobian = [[zero, zero]]
        g = [one, zero]
        self.assertEqual(rank(jacobian), 0)
        self.assertEqual(rank(jacobian + [g]), 1)
        # Mistakenly setting d=1 makes all size-2 minors vanish.
        self.assertTrue(all_minors_zero(jacobian + [g], 2))
        self.assertFalse(all_minors_zero(jacobian + [g], 1))
        self.assertEqual(pivot_minor_values(jacobian, g, [], [], one)[1], g)


if __name__ == "__main__":
    unittest.main()

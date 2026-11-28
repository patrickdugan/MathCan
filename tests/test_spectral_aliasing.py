"""SPC-01 independent exact F_5 Fourier and sparsu-pilot oracles.

Corresponding Lean file: MathCan/SpectralAliasing.lean.
No floating-point arithmetic or third-party dependencies.
"""

from itertools import combinations, product
import unittest

ROOTS = (1, 2, 4, 3)


def synthesis(coeff, phase):
    return sum(coeff[f] * ROOTS[(f * phase) % 4] for f in range(4)) % 5


def determinant_mod5(matrix):
    n = len(matrix)
    a = [[x % 5 for x in row] for row in matrix]
    det = 1
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col] % 5), None)
        if pivot is None:
            return 0
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            det = -det
        v = a[col][col] % 5
        det = det * v % 5
        inv = pow(v, -1, 5)
        for r in range(col + 1, n):
            z = a[r][col] * inv % 5
            for c in range(col, n):
                a[r][c] = (a[r][c] - z * a[col][c]) % 5
    return det % 5


class ExactFourierCertificate(unittest.TestCase):
    def test_root_and_orthogonality(self):
        self.assertEqual(pow(2, 4, 5), 1)
        self.assertEqual(len(set(ROOTS)), 4)
        for frequency in range(4):
            self.assertEqual(sum(ROOTS[(frequency * s) % 4]
                                 for s in range(4)) % 5,
                             4 if frequency == 0 else 0)

    def test_consecutive_pilots_are_full_spark(self):
        for r in range(1, 5):
            for frequencies in combinations(range(4), r):
                matrix = [[ROOTS[(s * f) % 4] for f in frequencies]
                          for s in range(r)]
                self.assertNotEqual(determinant_mod5(matrix), 0)

    def test_one_sparse_two_pilots_uniqueness(self):
        seen = set()
        for f in range(4):
            for a in range(1, 5):
                vector = [a if j == f else 0 for j in range(4)]
                signature = (synthesis(vector, 0), synthesis(vector, 1))
                self.assertNotIn(signature, seen)
                seen.add(signature)
        self.assertEqual(len(seen), 16)

    def test_two_sparse_three_pilot_witness(self):
        a, b = (1, 2, 0, 0), (0, 0, 1, 2)
        self.assertEqual(tuple(synthesis(a, s) for s in range(3)),
                         tuple(synthesis(b, s) for s in range(3)))
        self.assertNotEqual(synthesis(a, 3), synthesis(b, 3))

    def test_two_phases_detect_every_two_sparse_source(self):
        vectors = [v for v in product(range(5), repeat=4)
                   if sum(x != 0 for x in v) <= 2]
        for v in vectors:
            if synthesis(v, 0) == 0 and synthesis(v, 1) == 0:
                self.assertEqual(v, (0, 0, 0, 0))
        self.assertEqual((synthesis((1, 4, 0, 0), 0),
                          synthesis((1, 4, 0, 0), 1)), (0, 4))

    def test_four_pilots_recover_all_625_vectors(self):
        signatures = {tuple(synthesis(v, s) for s in range(4))
                      for v in product(range(5), repeat=4)}
        self.assertEqual(len(signatures), 5 ** 4)


if __name__ == "__main__":
    unittest.main()

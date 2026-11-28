"""NRF-08: 1200 rational projector/product checks and counterexamples."""
import random
import unittest
from fractions import Fraction as F
from research.compactification.suffix_leakage_transport import (
    matrix, mmul, identity, rational_projector, block_transport,
    frobenius_squared, interference, check_energy,
)

class SuffixTransportTests(unittest.TestCase):
    def test_shear_constructive_dark_injection(self):
        P = matrix([[1, 0], [0, 0]])
        J = matrix([[1, 2], [0, 1]])
        S = matrix([[1, 3], [0, 1]])
        old, A, B, total = block_transport(P, S, J)
        self.assertEqual(old[0][1], 2)
        self.assertEqual(A[0][1], 2)
        self.assertEqual(B[0][1], 3)
        self.assertEqual(total[0][1], 5)
        self.assertEqual(interference(A, B), F(12))
        self.assertTrue(check_energy(A, B, total))

    def test_rotation_leakage_can_cancel(self):
        P = matrix([[1, 0], [0, 0]])
        J = matrix([[0, -1], [1, 0]])
        old, A, B, total = block_transport(P, J, J)
        self.assertEqual(frobenius_squared(old), 1)
        self.assertEqual(frobenius_squared(total), 0)
        self.assertTrue(check_energy(A, B, total))

    def test_1200_exact_rational_cases(self):
        r = random.Random(808)
        for _ in range(1200):
            t = F(r.randint(-7, 7), r.randint(1, 9))
            P = rational_projector(t)
            self.assertEqual(mmul(P, P), P)
            J = matrix([[F(r.randint(-8, 8), 7) for _ in range(2)]
                        for _ in range(2)])
            S = matrix([[F(r.randint(-8, 8), 7) for _ in range(2)]
                        for _ in range(2)])
            _, A, B, total = block_transport(P, S, J)
            self.assertTrue(check_energy(A, B, total))

    def test_three_dimensional_block(self):
        P = matrix([[1, 0, 0], [0, 1, 0], [0, 0, 0]])
        J = matrix([[1, 2, -1], [3, 4, 5], [6, -7, 8]])
        S = matrix([[0, -2, 3], [4, 1, -1], [6, 7, 3]])
        _, A, B, total = block_transport(P, S, J)
        self.assertTrue(check_energy(A, B, total))

    def test_dimensions(self):
        with self.assertRaises(ValueError):
            matrix([[1, 2]])
        with self.assertRaises(ValueError):
            mmul(identity(2), identity(3))

if __name__ == "__main__":
    unittest.main()

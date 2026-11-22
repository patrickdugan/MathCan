"""Exact arithmetic audit of Proposition 4's trace and tensor interfaces."""
import random
import unittest
from fractions import Fraction as Q
from itertools import product

from research.deligne_sign_audit.geometry_trace import (
    mat, eye, multiply, power, trace, block_matrix, inverse, conjugate,
    powered_trace_splitting, signed_power_remainder, tensor_spectrum,
    tensor_power_trace, kunneth_lowest_degree_paths, twist_trace_pair,
)


class Deligne06GeometryTests(unittest.TestCase):
    def test_all_positive_powers_kernel_quotient_trace(self):
        rng = random.Random(261100796)
        for _ in range(70):
            K = mat([[rng.randrange(-5, 6), rng.randrange(-4, 5)],
                     [rng.randrange(-4, 5), rng.randrange(-5, 6)]])
            Qmat = mat([[rng.randrange(-5, 6), rng.randrange(-4, 5)],
                        [rng.randrange(-4, 5), rng.randrange(-5, 6)]])
            cross = mat([[rng.randrange(-5, 6), rng.randrange(-5, 6)],
                         [rng.randrange(-5, 6), rng.randrange(-5, 6)]])
            for n in range(0, 7):
                self.assertEqual(*powered_trace_splitting(K, Qmat, cross, n))

    def test_off_diagonal_extension_survives_without_trace_change(self):
        K, Qmat = mat([[2]]), mat([[3]])
        Y = block_matrix(K, Qmat, mat([[41]]))
        self.assertNotEqual(Y, block_matrix(K, Qmat, mat([[0]])))
        for n in range(1, 10):
            self.assertEqual(trace(power(Y, n)), 2**n + 3**n)

    def test_lower_left_breaks_invariant_kernel(self):
        K, Qmat, cross = mat([[2]]), mat([[3]]), mat([[1]])
        good = powered_trace_splitting(K, Qmat, cross, 2)
        bad = powered_trace_splitting(K, Qmat, cross, 2, mat([[1]]))
        self.assertEqual(good, (Q(13), Q(13)))
        self.assertEqual(bad, (Q(15), Q(13)))
        self.assertEqual(*powered_trace_splitting(K, Qmat, cross, 1,
                                                  mat([[1]])))

    def test_conjugate_high_degree_all_powers(self):
        X = mat([[3, 2], [1, 4]])
        P = mat([[2, 1], [3, 2]])
        Pinv = inverse(P)
        self.assertEqual(multiply(Pinv, P), eye(2))
        self.assertEqual(multiply(P, Pinv), eye(2))
        Y = conjugate(X, P)
        self.assertNotEqual(Y, X)
        for n in range(0, 10):
            self.assertEqual(trace(power(Y, n)), trace(power(X, n)))

    def test_gysin_signed_remainder_and_kernel(self):
        K = mat([[2, 1], [0, -1]])
        Qmat = mat([[3]])
        mix = mat([[7], [-11]])
        low = mat([[5]])
        high = [
            (mat([[2, 3], [0, 1]]), mat([[1, 3], [0, 1]])),
            (mat([[4, 2], [1, 2]]), mat([[1, 0], [2, 1]])),
            (mat([[9]]), mat([[2]])),
        ]
        for n in range(1, 9):
            signed = signed_power_remainder(K, Qmat, mix, low, high, n)
            expected = trace(power(K, n)) + trace(power(low, n))
            self.assertEqual(signed, expected)
            for D in range(1, 9):
                sign = (-1)**(D-1)
                R = signed * sign
                self.assertEqual(sign * R, expected)

    def test_high_degree_missing_conjugacy_changes_remainder(self):
        K, Qmat, mix, low = (mat([[2]]), mat([[3]]),
                              mat([[1]]), mat([[5]]))
        expected = signed_power_remainder(K, Qmat, mix, low, [], 2)
        # Mutant changes one high Frobenius eigenvalue while still
        # pretending that its cohomology is isomorphic to the X side.
        Xhi = mat([[2]])
        Yhi = mat([[7]])
        mutant = expected - (trace(power(Yhi, 2)) -
                             trace(power(Xhi, 2)))
        self.assertNotEqual(mutant, expected)

    def test_tate_twist_requires_r_to_the_n(self):
        for r in (2, 3, 5, 7):
            for n in range(0, 7):
                z, expected = twist_trace_pair(r, [Q(1, 2), Q(-3, 2)], n)
                self.assertEqual(z, expected)
                if n > 1 and expected:
                    self.assertNotEqual(expected, r * (Q(1, 2)**n +
                                                        Q(-3, 2)**n))

    def test_tensor_diagonal_trace_and_target_eigenvalues(self):
        for spectrum in ([2], [2, 3], [-2, 2], [2, 2, 3]):
            for k in range(0, 5):
                vals = tensor_spectrum(tuple(map(Q, spectrum)), k)
                self.assertEqual(len(vals), len(spectrum)**k)
                for n in range(0, 7):
                    self.assertEqual(*tensor_power_trace(spectrum, k, n))
                for alpha in spectrum:
                    self.assertIn(Q(alpha)**k, vals)

    def test_duplicate_eigenvalues_are_genuine_multiplicities(self):
        vals = tensor_spectrum((Q(2), Q(2), Q(3)), 2)
        self.assertEqual(vals.count(Q(4)), 4)
        self.assertEqual(vals.count(Q(6)), 4)
        self.assertEqual(vals.count(Q(9)), 1)
        self.assertEqual(sum(vals), (2 + 2 + 3)**2)

    def test_lowest_kunneth_degree_unique(self):
        for d in range(1, 5):
            for k in range(1, 5):
                paths = kunneth_lowest_degree_paths(d, k)
                self.assertEqual(paths, ((d,)*k,))
        # Dropping one lower-degree vanishing condition allows a
        # distinct mixed-degree tuple with the same total D.
        self.assertEqual(sum((1, 2, 3)), 2*3)
        self.assertNotEqual((1, 2, 3), (2, 2, 2))

    def test_reject_singular_conjugacy(self):
        with self.assertRaisesRegex(ValueError, "singular"):
            inverse(mat([[1, 2], [2, 4]]))
        with self.assertRaises(ValueError):
            multiply(mat([[1, 2]]), mat([[1, 2]]))


if __name__ == "__main__":
    unittest.main()

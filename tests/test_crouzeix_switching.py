"""Exact finite arithmetic tests for the NRF-01 pure-math lemmas."""
import unittest
from fractions import Fraction as Q
from itertools import product
from research.compactification.crouzeix_switching import (
    jordan_disk_upper, phase_factor, amplification, weighted_disturbance,
    recursive_disturbance, cycles_disturbance, exact_jordan_polynomial,
    independent_jordan_eval,
)


class CrouzeixSwitchingMathTests(unittest.TestCase):
    def test_jordan_matrix_polynomial_oracle(self):
        trials = 0
        for shear, a0, a1, a2 in product(
            (Q(-3), Q(0), Q(2)),
            (Q(-1, 8), Q(0), Q(1, 7)),
            (Q(-1, 6), Q(0), Q(1, 6)),
            (Q(0), Q(1, 12)),
        ):
            coeff = (a0, a1, a2)
            self.assertEqual(exact_jordan_polynomial(shear, coeff),
                             independent_jordan_eval(shear, coeff))
            self.assertGreaterEqual(jordan_disk_upper(shear, coeff), 0)
            trials += 1
        self.assertEqual(trials, 54)

    def test_weighted_telescope_exhaustive(self):
        rateset = (Q(0), Q(1, 4), Q(1), Q(3, 2))
        trials = 0
        for k in range(1, 4):
            for r in product(rateset, repeat=k):
                for d in product((Q(0), Q(1, 20)), repeat=k):
                    self.assertEqual(weighted_disturbance(r, d),
                                     recursive_disturbance(r, d))
                    trials += 1
        self.assertEqual(trials, 8 + 64 + 512)

    def test_expansive_phase_compensation(self):
        factors = (phase_factor(Q(1), Q(1)), phase_factor(Q(3, 4), Q(0)))
        self.assertEqual(factors, (Q(2), Q(1, 4)))
        self.assertEqual(amplification(factors), Q(1, 2))
        self.assertEqual(cycles_disturbance(factors, (Q(1, 100), Q(1, 100)), 3),
                         weighted_disturbance(factors, (Q(1, 100), Q(1, 100))) * Q(7, 4))

    def test_nonnormal_spectrum_obstruction(self):
        a = exact_jordan_polynomial(Q(2), (Q(0), Q(1)))
        self.assertEqual(a, ((Q(0), Q(2)), (Q(0), Q(0))))
        self.assertEqual(jordan_disk_upper(Q(2), (Q(0), Q(1))), Q(1))
        self.assertEqual(2 * jordan_disk_upper(Q(2), (Q(0), Q(1))), Q(2))

    def test_failure_guards(self):
        with self.assertRaises(ValueError):
            phase_factor(Q(2), Q(0))
        with self.assertRaises(ValueError):
            jordan_disk_upper(Q(1), ())
        with self.assertRaises(ValueError):
            weighted_disturbance((Q(1),), ())
        with self.assertRaises(ValueError):
            cycles_disturbance((Q(1),), (Q(0),), 2)


if __name__ == "__main__":
    unittest.main()

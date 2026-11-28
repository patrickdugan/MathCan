import importlib.util
from fractions import Fraction
from pathlib import Path
import unittest

SRC = Path(__file__).resolve().parents[1] / 'research' / 'orbit_lock' / 'oracle.py'
spec = importlib.util.spec_from_file_location('orbit_lock_oracle', SRC)
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


class OrbitLockTests(unittest.TestCase):
    def test_matching_counts(self):
        for n, count in [(2, 1), (4, 3), (6, 15), (8, 105)]:
            self.assertEqual(len(tuple(oracle.matchings(range(n)))), count)

    def test_exact_orbit_and_noisy_laws(self):
        for n in (4, 6):
            for noise in (Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(1)):
                row = oracle.orbit_certificate(n, noise)
                m = row['matching_count']
                self.assertEqual(Fraction(row['tv']), (1 - noise) * Fraction(m - 1, m))
                self.assertEqual(row['marginal_tv'], '0')
                self.assertEqual(Fraction(row['optimal_event_probability']), 1 - noise + noise / m)

    def test_action_is_a_group_action(self):
        match = next(oracle.matchings(range(4)))
        p, q = (2, 0, 3, 1), (1, 3, 0, 2)
        pq = tuple(p[q[i]] for i in range(4))
        self.assertEqual(oracle.action(pq, match), oracle.action(p, oracle.action(q, match)))

    def test_bad_input(self):
        for n, eps in ((3, Fraction(0)), (4, Fraction(-1, 2)), (6, Fraction(2))):
            with self.assertRaises(ValueError):
                oracle.orbit_certificate(n, eps)


if __name__ == '__main__':
    unittest.main()

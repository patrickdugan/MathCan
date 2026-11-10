import itertools
import unittest
from fractions import Fraction as F
from research.chitraverse.cycle_potentials import (
    IntervalEdge, multiplicative_potential, verify_potential,
    profitable_cycle, certify_intervals, cycle_conversion)


class PotentialTests(unittest.TestCase):
    def test_exhaustive_rational_three_vertex_graphs(self):
        n = 3
        candidates = ((0, 1), (1, 2), (2, 0), (0, 2), (2, 1), (1, 0))
        # 4^6 = 4,096 complete rate-or-absence configurations.
        for configuration in itertools.product((None, F(1, 2), F(1), F(2)), repeat=6):
            rates = tuple((u, v, r) for (u, v), r in zip(candidates, configuration)
                          if r is not None)
            potential = multiplicative_potential(n, rates)
            cycle = profitable_cycle(n, rates)
            self.assertEqual(potential is None, cycle is not None)
            if potential is not None:
                self.assertTrue(verify_potential(n, rates, potential))
            if cycle is not None:
                result = F(1)
                prev = rates[cycle[-1]][1]
                for idx in cycle:
                    u, v, r = rates[idx]
                    self.assertEqual(u, prev)
                    prev = v
                    result *= r
                self.assertGreater(result, 1)

    def test_robust_no_cycle_with_high_rates(self):
        edges = (IntervalEdge(0, 1, F(1, 2), F(3, 2)),
                 IntervalEdge(1, 0, F(1, 4), F(1, 2)))
        label, cert = certify_intervals(2, edges)
        self.assertEqual(label, 'robust_no_cycle')
        self.assertTrue(verify_potential(2, ((e.source, e.target, e.upper) for e in edges), cert))

    def test_guaranteed_and_unresolved(self):
        strong = (IntervalEdge(0, 1, F(2), F(3)),
                  IntervalEdge(1, 0, F(1), F(2)))
        self.assertEqual(certify_intervals(2, strong)[0], 'guaranteed_cycle')
        variable = (IntervalEdge(0, 1, F(1), F(2)),
                    IntervalEdge(1, 0, F(1, 2), F(1)))
        self.assertEqual(certify_intervals(2, variable)[0], 'unresolved')

    def test_nonlinear_marginal_criterion(self):
        no_cycle = ((F(3, 2), F(1, 2)), (F(1, 2), F(2)))
        for k in range(1, 35):
            x = F(k, 100)
            self.assertLessEqual(cycle_conversion(x, no_cycle), x)
        profitable = ((F(2), F(1)), (F(1), F(1)))
        for k in range(1, 20):
            x = F(1, k*100)
            self.assertGreater(cycle_conversion(x, profitable), x)

    def test_self_loop(self):
        self.assertIsNone(multiplicative_potential(1, ((0, 0, F(5, 4)),)))
        self.assertEqual(profitable_cycle(1, ((0, 0, F(5, 4)),)), (0,))
        self.assertIsNotNone(multiplicative_potential(1, ((0, 0, F(4, 5)),)))


if __name__ == '__main__':
    unittest.main()

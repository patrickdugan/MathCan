"""CHTR-02 exact finite regression and adversarial checks."""
import itertools
import random
import unittest
from fractions import Fraction as F
from research.chitraverse.hodge_arbitrage import (
    hodge_certificate, signed_cycle_bound, robust_nonzero_obstruction,
    robust_cycle_energy_lower_bound,
)


class HodgeArbitrageTests(unittest.TestCase):
    def test_single_cycle_sharp_closed_form(self):
        edges = ((0, 1), (1, 2), (2, 0))
        for quotes in itertools.product((F(-1), F(0), F(1), F(2)), repeat=3):
            for weights in ((F(1), F(1), F(1)),
                            (F(1), F(2), F(3)),
                            (F(2), F(5), F(7))):
                out = hodge_certificate(3, edges, quotes, weights)
                hol = sum(quotes, F(0))
                expected = hol * hol / sum((1 / x for x in weights), F(0))
                self.assertEqual(out.cycle_basis, ((1, 1, 1),))
                self.assertEqual(out.holonomies, (hol,))
                self.assertEqual(out.energy, expected)
                self.assertEqual(signed_cycle_bound(3, edges, quotes, weights,
                                                    (1, 1, 1)), expected)
                self.assertEqual(sum((w * r for w, r in zip(weights, out.residual)), F(0)), 3 * out.dual_multipliers[0])

    def test_multi_cycle_gauge_invariance_and_reconstruction(self):
        edges = ((0, 1), (1, 2), (2, 3), (3, 0), (0, 2))
        rng = random.Random(1729)
        for _ in range(150):
            quotes = tuple(F(rng.randint(-9, 9), rng.randint(1, 7))
                           for _ in edges)
            weights = tuple(F(rng.randint(1, 7), rng.randint(1, 5))
                            for _ in edges)
            cert = hodge_certificate(4, edges, quotes, weights)
            self.assertEqual(len(cert.cycle_basis), 2)
            self.assertEqual(sum((weights[i] * cert.residual[i] ** 2
                                  for i in range(len(edges))), F(0)), cert.energy)
            self.assertEqual(sum((weights[i] * (quotes[i] - (cert.node_potentials[v] - cert.node_potentials[u])) ** 2
                                  for i, (u, v) in enumerate(edges)), F(0)), cert.energy)
            self.assertGreaterEqual(cert.energy, 0)
            for row in cert.cycle_basis:
                bound = signed_cycle_bound(4, edges, quotes, weights, row)
                self.assertGreaterEqual(cert.energy, bound)
            cycle = tuple(cert.cycle_basis[0][i] - 2 * cert.cycle_basis[1][i]
                          for i in range(len(edges)))
            self.assertGreaterEqual(cert.energy,
                                    signed_cycle_bound(4, edges, quotes, weights, cycle))
            offset = tuple(F(rng.randint(-10, 10), 3) for _ in range(4))
            shifted = tuple(quotes[i] + offset[v] - offset[u]
                            for i, (u, v) in enumerate(edges))
            gauge = hodge_certificate(4, edges, shifted, weights)
            self.assertEqual(gauge.energy, cert.energy)
            self.assertEqual(gauge.residual, cert.residual)
            self.assertEqual(gauge.holonomies, cert.holonomies)
            # Flipping an arbitrary physical edge direction preserves E.
            j = rng.randrange(len(edges))
            flipped_edges = list(edges)
            flipped_edges[j] = tuple(reversed(flipped_edges[j]))
            flipped_quotes = list(quotes)
            flipped_quotes[j] = -flipped_quotes[j]
            flip = hodge_certificate(4, flipped_edges, flipped_quotes, weights)
            self.assertEqual(flip.energy, cert.energy)
            self.assertEqual(flip.residual[j], -cert.residual[j])

    def test_tree_is_exact_even_for_arbitrary_quotes(self):
        edges = ((0, 1), (2, 1), (1, 3), (4, 3))
        quotes = (F(2, 3), F(-8), F(15, 4), F(11, 9))
        cert = hodge_certificate(5, edges, quotes, (1, 4, 2, 7))
        self.assertEqual(cert.energy, 0)
        self.assertEqual(cert.cycle_basis, ())
        self.assertEqual(cert.gradient, quotes)
        self.assertTrue(all(r == 0 for r in cert.residual))

    def test_parallel_edges_form_cycle(self):
        edges = ((0, 1), (0, 1))
        c = hodge_certificate(2, edges, (F(1), F(0)), (F(1), F(1)))
        self.assertEqual(c.energy, F(1, 2))
        self.assertEqual(abs(c.holonomies[0]), 1)

    def test_robust_claim_exact_adversarial_corners(self):
        edges = ((0, 1), (1, 2), (2, 0))
        q = (F(1), F(0), F(0))
        weights = (F(1),) * 3
        errors = (F(1, 10),) * 3
        c = hodge_certificate(3, edges, q, weights)
        self.assertTrue(robust_nonzero_obstruction(c.energy, weights, errors))
        for noise in itertools.product((-1, 0, 1), repeat=3):
            true_q = tuple(q[i] + noise[i] * errors[i] for i in range(3))
            self.assertGreater(hodge_certificate(3, edges, true_q, weights).energy, 0)
        self.assertFalse(robust_nonzero_obstruction(c.energy, weights, (F(1),) * 3))
        self.assertFalse(robust_nonzero_obstruction(F(0), weights, errors))

    def test_interval_cycle_bound_sharp_and_stronger_than_ball(self):
        tri = ((0, 1), (1, 2), (2, 0))
        observed = (F(1), F(0), F(0))
        weights = (F(1),) * 3
        errors = (F(1, 5),) * 3
        lower = robust_cycle_energy_lower_bound(3, tri, observed, weights,
                                                errors, (1, 1, 1))
        self.assertEqual(lower, F(4, 75))
        witness = tuple(observed[i] - errors[i] for i in range(3))
        self.assertEqual(hodge_certificate(3, tri, witness, weights).energy, lower)
        # When the cycle interval contains zero holonomy, the infimum is zero.
        self.assertEqual(robust_cycle_energy_lower_bound(3, tri, observed, weights,
                         (F(1, 2),) * 3, (1, 1, 1)), 0)
        self.assertEqual(hodge_certificate(3, tri, (F(1, 2), F(-1, 2), F(0)),
                                           weights).energy, 0)
        # A bridge may have huge measurement error without affecting cycles.
        graph = tri + ((2, 3),)
        q = observed + (F(37),)
        w = weights + (F(100),)
        e = errors + (F(10),)
        cert = hodge_certificate(4, graph, q, w)
        self.assertFalse(robust_nonzero_obstruction(cert.energy, w, e))
        self.assertEqual(robust_cycle_energy_lower_bound(4, graph, q, w, e,
                                                         (1, 1, 1, 0)), lower)
        for signs in itertools.product((-1, 1), repeat=4):
            true_q = tuple(q[i] + signs[i] * e[i] for i in range(4))
            self.assertGreaterEqual(hodge_certificate(4, graph, true_q, w).energy,
                                    lower)

    def test_failure_modes_and_invalid_circulations(self):
        with self.assertRaises(ValueError):
            hodge_certificate(3, ((0, 1),), (0,), (1,))
        with self.assertRaises(ValueError):
            hodge_certificate(2, ((0, 0),), (0,), (1,))
        with self.assertRaises(ValueError):
            hodge_certificate(2, ((0, 1),), (0,), (0,))
        with self.assertRaises(ValueError):
            signed_cycle_bound(3, ((0, 1), (1, 2), (2, 0)),
                               (1, 1, 1), (1, 1, 1), (1, 0, 0))
        with self.assertRaises(ValueError):
            robust_nonzero_obstruction(0, (1, 0), (1, 1))


if __name__ == '__main__':
    unittest.main()
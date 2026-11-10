"""Independent exact rational checks of CHTR-03 finite hook automata."""
import itertools
import random
import unittest
from fractions import Fraction as Q

from research.chitraverse.stateful_hooks import (
    Hook, validate, index, state_node, lifted_edges, potential, verify_potential,
    execute, profitable_closed_cycle, snapshot_potentials, best_gain_by_horizon,
    gauge_rates, commuting_order_ratio, interval_certificate,
    quotient_upper_certificate,
)
from research.chitraverse.cycle_potentials import profitable_cycle


class StatefulHooksTests(unittest.TestCase):
    def test_frozen_no_arbitrage_but_dynamic_cycle_gain_four(self):
        # Both price snapshots have forward*backward=1. Hooks toggle state.
        hooks = (
            Hook('A-to-B', 0, 1, (1, 0), (Q(2), Q(1, 2))),
            Hook('B-to-A', 1, 0, (1, 0), (Q(1, 2), Q(2))),
        )
        snapshots = snapshot_potentials(2, 2, hooks)
        self.assertTrue(all(p is not None for p in snapshots))
        self.assertIsNone(potential(2, 2, hooks))
        end, gain, trace = execute(2, 2, hooks, (0, 0), (0, 1))
        self.assertEqual(end, (0, 0))
        self.assertEqual(gain, 4)
        self.assertEqual(trace, ((0, 0), (1, 1), (0, 0)))
        cert = profitable_closed_cycle(2, 2, hooks)
        self.assertIsNotNone(cert)
        self.assertEqual(cert.gain, 4)
        self.assertEqual(cert.trace[0], cert.trace[-1])
        self.assertEqual(best_gain_by_horizon(2, 2, hooks, (0, 0), 2)[(0, 0)][0], 4)
        self.assertEqual(best_gain_by_horizon(2, 2, hooks, (0, 0), 4)[(0, 0)][0], 16)

    def test_exhaustive_rate_tables_agree_with_independent_simple_cycle_oracle(self):
        # 625 networks: four independently varying rates (two hooks, two states).
        options = (Q(1, 4), Q(1, 2), Q(1), Q(2), Q(4))
        for rates in itertools.product(options, repeat=4):
            hooks = (Hook('f', 0, 1, (1, 0), rates[:2]),
                     Hook('g', 1, 0, (1, 0), rates[2:]))
            cert = potential(2, 2, hooks)
            # The exhaustive simple-cycle oracle is independent of Bellman-Ford.
            witness_indices = profitable_cycle(4, lifted_edges(2, 2, hooks))
            self.assertEqual(cert is None, witness_indices is not None)
            self.assertEqual(profitable_closed_cycle(2, 2, hooks) is not None,
                             cert is None)
            if cert is not None:
                self.assertTrue(verify_potential(2, 2, hooks, cert))

    def test_gauge_telescopes_and_preserves_closed_gain(self):
        hooks = (
            Hook('f', 0, 1, (1, 0), (Q(3, 2), Q(2, 3))),
            Hook('g', 1, 0, (1, 0), (Q(5, 4), Q(4, 5))),
            Hook('x', 0, 0, (0, 1), (Q(7, 3), Q(11, 5))),
        )
        gauge = (Q(5), Q(7), Q(11), Q(13))
        transformed = gauge_rates(2, 2, hooks, gauge)
        for start in ((0, 0), (0, 1), (1, 0), (1, 1)):
            for word in ((), (2,), (2, 2), (0, 1), (0, 1, 2), (1, 0)):
                try:
                    end, gain, _ = execute(2, 2, hooks, start, word)
                except ValueError:
                    continue
                end2, new_gain, _ = execute(2, 2, transformed, start, word)
                self.assertEqual(end, end2)
                self.assertEqual(new_gain, gain * gauge[index(*start, 2)] /
                                 gauge[index(*end, 2)])
                if end == start:
                    self.assertEqual(new_gain, gain)
        self.assertEqual(potential(2, 2, hooks) is None,
                         potential(2, 2, transformed) is None)

    def test_order_curvature_only_for_common_endpoint_and_gauge_invariant(self):
        # Distinct rates at different states create order-dependent gain.
        hooks = (Hook('alpha', 0, 0, (1, 0), (Q(1, 2), Q(1, 2))),
                 Hook('beta', 0, 0, (0, 1), (Q(3, 4), Q(1, 4))))
        self.assertEqual(commuting_order_ratio(1, 2, hooks, 0, 1, (0, 0)), Q(1, 3))
        gauged = gauge_rates(1, 2, hooks, (Q(11), Q(3)))
        self.assertEqual(commuting_order_ratio(1, 2, gauged, 0, 1, (0, 0)), Q(1, 3))
        # Noncommuting updates: the end-state mismatch makes the ratio gauge-dependent.
        hooks_bad = (Hook('alpha', 0, 0, (1, 0, 2), (1, 1, 1)),
                     Hook('beta', 0, 0, (0, 2, 1), (1, 1, 1)))
        with self.assertRaises(ValueError):
            commuting_order_ratio(1, 3, hooks_bad, 0, 1, (0, 0))

    def test_sound_interval_upper_and_lower_certificates(self):
        hooks = (Hook('f', 0, 1, (1, 0), (1, 1)),
                 Hook('g', 1, 0, (1, 0), (1, 1)))
        lower = ((Q(1, 2), Q(1, 4)), (Q(1, 4), Q(1, 2)))
        upper = ((Q(3, 4), Q(3, 4)), (Q(3, 4), Q(3, 4)))
        label, witness = interval_certificate(2, 2, hooks, lower, upper)
        self.assertEqual(label, 'robust_no_cycle')
        for a in itertools.product((0, 1), repeat=4):
            rates = [low[s] if a[i*2+s] == 0 else upper[i][s]
                     for i, low in enumerate(lower) for s in range(2)]
            changed = (Hook('f', 0, 1, (1, 0), rates[:2]),
                       Hook('g', 1, 0, (1, 0), rates[2:]))
            self.assertTrue(verify_potential(2, 2, changed, witness))
        low = ((Q(2), Q(1, 2)), (Q(1, 2), Q(2)))
        hi = ((Q(3), Q(1)), (Q(1), Q(3)))
        label, cyc = interval_certificate(2, 2, hooks, low, hi)
        self.assertEqual(label, 'guaranteed_closed_cycle')
        self.assertGreater(cyc.gain, 1)
        label, witness = interval_certificate(2, 2, hooks, ((Q(1, 4),)*2,)*2,
                                               ((Q(4),)*2,)*2)
        self.assertEqual((label, witness), ('unresolved', None))

    def test_quotient_potential_sound_but_false_positive_can_arise(self):
        # The abstract singleton state uses edgewise maxima 2*2=4.
        # Concrete cycles have product 1/2 or 1 and no positive loop.
        hooks = (Hook('f', 0, 1, (1, 0), (Q(2), Q(1, 2))),
                 Hook('g', 1, 0, (1, 0), (Q(2), Q(1, 4))))
        self.assertIsNotNone(potential(2, 2, hooks))
        self.assertIsNone(quotient_upper_certificate(2, 2, hooks, (0, 0)))
        # When quotient upper constraints pass, their pullback is a concrete witness.
        safe = (Hook('f', 0, 1, (1, 0), (Q(1, 2), Q(2, 3))),
                Hook('g', 1, 0, (1, 0), (Q(1, 2), Q(1, 2))))
        pair = quotient_upper_certificate(2, 2, safe, (0, 0))
        self.assertIsNotNone(pair)
        self.assertTrue(verify_potential(2, 2, safe, pair[1]))
        bad_partition = (Hook('f', 0, 1, (1, 2, 2), (1, 1, 1)),)
        with self.assertRaises(ValueError):
            quotient_upper_certificate(2, 3, bad_partition, (0, 0, 1))

    def test_bounded_horizon_matches_independent_exhaustive_enumeration(self):
        rng = random.Random(1734)
        for _ in range(100):
            hooks = (Hook('f', 0, 1, (rng.randrange(2), rng.randrange(2)),
                          (Q(rng.randint(1, 4), 2), Q(rng.randint(1, 4), 3))),
                     Hook('g', 1, 0, (rng.randrange(2), rng.randrange(2)),
                          (Q(rng.randint(1, 4), 2), Q(rng.randint(1, 4), 3))),
                     Hook('h', 0, 0, (rng.randrange(2), rng.randrange(2)),
                          (Q(rng.randint(1, 4), 2), Q(rng.randint(1, 4), 3))))
            start = (0, rng.randrange(2))
            computed = best_gain_by_horizon(2, 2, hooks, start, 4)
            brute = {start: Q(1)}
            for k in range(1, 5):
                for word in itertools.product(range(len(hooks)), repeat=k):
                    try:
                        end, gain, _ = execute(2, 2, hooks, start, word)
                    except ValueError:
                        continue
                    brute[end] = max(gain, brute.get(end, Q(0)))
            self.assertEqual({key: x[0] for key, x in computed.items()}, brute)
            for end, (gain, word) in computed.items():
                endpoint, value, _ = execute(2, 2, hooks, start, word)
                self.assertEqual((endpoint, value), (end, gain))

    def test_directed_no_arbitrage_can_have_nonzero_undirected_hodge_energy(self):
        # A DAG has no directed cycles, but the underlying undirected triangle
        # can carry a nonzero Hodge residual. These are distinct obstructions.
        from research.chitraverse.hodge_arbitrage import hodge_certificate
        hooks = (Hook('ab', 0, 1, (0,), (Q(2),)),
                 Hook('bc', 1, 2, (0,), (Q(2),)),
                 Hook('ac', 0, 2, (0,), (Q(2),)))
        self.assertIsNotNone(potential(3, 1, hooks))
        self.assertIsNone(profitable_closed_cycle(3, 1, hooks))
        cert = hodge_certificate(3, ((0, 1), (1, 2), (0, 2)),
                                 (Q(1), Q(1), Q(1)), (Q(1),)*3)
        self.assertEqual(cert.energy, Q(1, 3))

    def test_nonlinear_cpmm_hook_state_and_two_leg_roundtrip(self):
        from research.chitraverse.nonlinear_pool import Pool, swap, two_leg_roundtrip
        for reserve_a in (Q(1), Q(7), Q(31, 2)):
            for reserve_b in (Q(2), Q(11)):
                for amount in (Q(1, 10), Q(1), Q(9)):
                    for gamma1 in (Q(1, 2), Q(3, 4), Q(1)):
                        for gamma2 in (Q(1, 2), Q(3, 4), Q(1)):
                            pool = Pool(reserve_a, reserve_b)
                            later, back, forward = two_leg_roundtrip(
                                pool, amount, gamma1, gamma2,
                                interim_state=9, final_state=0)
                            self.assertGreater(forward, 0)
                            self.assertLessEqual(back, amount)
                            self.assertGreaterEqual(later.reserve_product,
                                                    pool.reserve_product)
                            self.assertEqual(later.hook_state, 0)
                            if gamma1 == gamma2 == 1:
                                self.assertEqual(back, amount)
                                self.assertEqual(later.reserve_product,
                                                 pool.reserve_product)
        with self.assertRaises(ValueError):
            swap(Pool(10, 20), 'A', 1, Q(3, 2))
        with self.assertRaises(ValueError):
            swap(Pool(10, 20), 'C', 1, 1)

    def test_invalid_inputs(self):
        with self.assertRaises(ValueError):
            validate(0, 2, ())
        with self.assertRaises(ValueError):
            validate(2, 2, (Hook('f', 0, 1, (0,), (1,)),))
        with self.assertRaises(ValueError):
            validate(2, 2, (Hook('f', 0, 1, (0, 1), (Q(0), Q(1))),))
        with self.assertRaises(ValueError):
            validate(2, 2, (Hook('f', 0, 1, (0, 1), (Q(1), Q(1))),
                            Hook('f', 1, 0, (0, 1), (Q(1), Q(1)))))
        with self.assertRaises(ValueError):
            interval_certificate(1, 1, (Hook('z', 0, 0, (0,), (Q(1),)),),
                                 ((Q(2),),), ((Q(1),),))
        self.assertEqual(state_node(3, 2), (1, 1))


if __name__ == '__main__':
    unittest.main()

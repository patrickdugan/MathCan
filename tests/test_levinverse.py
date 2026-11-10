"""Independent finite-state checks for LVR-01."""
import itertools
import unittest
from fractions import Fraction as F
from research.levinverse.finite_interventions import (
    refine_partition, shortest_distinguishing_word, coupling_bound,
    uniform_one_step_defect, micro_macro_history_error, total_variation)


class FiniteQuotientTests(unittest.TestCase):
    def test_exhaustive_three_states_two_actions(self):
        states = (0, 1, 2)
        actions = ('x', 'y')
        for targets in itertools.product(states, repeat=len(states) * len(actions)):
            step = {(s, a): targets[i * 2 + j]
                    for i, s in enumerate(states) for j, a in enumerate(actions)}
            for outputs in itertools.product((0, 1), repeat=len(states)):
                observe = dict(zip(states, outputs))
                labels, rounds = refine_partition(states, actions, step, observe)
                self.assertLessEqual(rounds, len(states) - len(set(outputs)))
                for s in states:
                    for t in states:
                        word = shortest_distinguishing_word(s, t, actions, step, observe)
                        self.assertEqual(labels[s] == labels[t], word is None)
                        if word is not None:
                            self.assertLessEqual(len(word), len(states) - 1)
                            s1, t1 = s, t
                            for a in word:
                                s1, t1 = step[(s1, a)], step[(t1, a)]
                            self.assertNotEqual(observe[s1], observe[t1])

    def test_actions_and_observations_are_monotone(self):
        states = (0, 1, 2, 3)
        step = {(s, a): (s + (1 if a == 'tick' else 0)) % 4
                for s in states for a in ('tick', 'stay')}
        fine = {s: s for s in states}
        coarse = {s: s % 2 for s in states}
        for obs in (fine, coarse):
            small, _ = refine_partition(states, ('stay',), step, obs)
            big, _ = refine_partition(states, ('stay', 'tick'), step, obs)
            for i in states:
                for j in states:
                    if big[i] == big[j]:
                        self.assertEqual(small[i], small[j])
        fine_labels, _ = refine_partition(states, ('tick',), step, fine)
        coarse_labels, _ = refine_partition(states, ('tick',), step, coarse)
        for i in states:
            for j in states:
                if fine_labels[i] == fine_labels[j]:
                    self.assertEqual(coarse_labels[i], coarse_labels[j])


class StochasticTests(unittest.TestCase):
    def test_tight_history_bound(self):
        e = F(1, 4)
        q = {0: 0, 1: 1}
        P = {(0, 'a'): {0: F(1)}, (1, 'a'): {1: F(1)}}
        Q = {(0, 'a'): {0: 1-e, 1: e}, (1, 'a'): {1: F(1)}}
        self.assertEqual(uniform_one_step_defect(P, Q, q, ('a',)), e)
        for T in range(8):
            err = micro_macro_history_error(0, P, Q, q, lambda _: 'a', T)
            self.assertEqual(err, coupling_bound(e, T))

    def test_quotient_and_adaptive_policy(self):
        q = {0: 'A', 1: 'A', 2: 'B'}
        P = {(0, 'a'): {0: F(3, 4), 2: F(1, 4)},
             (1, 'a'): {1: F(1)}, (2, 'a'): {2: F(1)},
             (0, 'b'): {1: F(1)}, (1, 'b'): {1: F(1)},
             (2, 'b'): {2: F(1)}}
        Q = {('A', 'a'): {'A': F(3, 4), 'B': F(1, 4)},
             ('B', 'a'): {'B': F(1)},
             ('A', 'b'): {'A': F(1)}, ('B', 'b'): {'B': F(1)}}
        eps = uniform_one_step_defect(P, Q, q, ('a', 'b'))
        self.assertEqual(eps, F(1, 4))
        def policy(history):
            return 'b' if len(history) % 2 == 0 else 'a'
        for T in range(7):
            self.assertLessEqual(micro_macro_history_error(0, P, Q, q, policy, T),
                                 coupling_bound(eps, T))

    def test_tv_symmetry(self):
        p = {'x': F(1, 3), 'y': F(2, 3)}
        q = {'x': F(2, 3), 'y': F(1, 3)}
        self.assertEqual(total_variation(p, q), F(1, 3))
        self.assertEqual(total_variation(p, q), total_variation(q, p))


if __name__ == '__main__':
    unittest.main()

"""NRF-05 exact rational dense-gate witnesses and counterexamples."""
from fractions import Fraction as Q
from itertools import product
import unittest

from research.compactification.global_gate_nogo import (
    full_linear_collapse_hypotheses, test_observation_closure,
)


class GlobalGateNoGoTests(unittest.TestCase):
    def test_all_nonzero_two_dimensional_observations(self):
        w1 = ((1, 2), (3, 5))
        w2 = ((2, 1), (1, 1))
        result = full_linear_collapse_hypotheses(w1, w2)
        self.assertTrue(result["full_linear_no_go"])
        self.assertEqual(result["w1_rank"], 2)
        self.assertEqual(result["w2_rank"], 2)
        count = 0
        for a, b in product(range(-2, 3), repeat=2):
            if a == 0 and b == 0:
                continue
            self.assertEqual(test_observation_closure(w1, w2, ((a, b),)), 2)
            count += 1
        self.assertEqual(count, 24)

    def test_three_dimensional_noncoordinate_observations(self):
        w1 = ((1, 1, 1), (1, 2, 1), (1, 1, 2))
        w2 = ((2, 1, 1), (1, 2, 1), (1, 1, 2))
        self.assertTrue(full_linear_collapse_hypotheses(w1, w2)["full_linear_no_go"])
        count = 0
        for row in product((-2, -1, 0, 1, 2), repeat=3):
            if all(v == 0 for v in row):
                continue
            self.assertEqual(test_observation_closure(w1, w2, (row,)), 3)
            count += 1
        self.assertEqual(count, 124)

    def test_reducible_system_retains_exact_one_dimensional_factor(self):
        eye = ((1, 0), (0, 1))
        receipt = full_linear_collapse_hypotheses(eye, eye)
        self.assertFalse(receipt["full_linear_no_go"])
        self.assertEqual(receipt["zero_interaction_entries"], 2)
        self.assertEqual(test_observation_closure(eye, eye, ((1, 0),)), 1)

    def test_singular_activations_fail_sufficient_hypotheses(self):
        w1 = ((1, 1), (2, 2))
        w2 = ((2, 1), (1, 1))
        receipt = full_linear_collapse_hypotheses(w1, w2)
        self.assertEqual(receipt["w1_rank"], 1)
        self.assertFalse(receipt["full_linear_no_go"])

    def test_strict_dimension_check(self):
        with self.assertRaises(ValueError):
            full_linear_collapse_hypotheses(((1, 0),), ((1, 0),))
        with self.assertRaises(ValueError):
            full_linear_collapse_hypotheses(((1, 0), (0, 1)), ((1,),))


if __name__ == "__main__":
    unittest.main()

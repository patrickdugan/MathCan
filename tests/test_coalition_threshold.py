"""PEF-06T independent exact finite integer oracle."""
import unittest
from itertools import product


def add(x,y):
    return x+y


def mul(x,y):
    return x*y


class CoalitionThresholdTests(unittest.TestCase):
    def test_additive_four_corner_identity_for_all_small_integer_states(self):
        for x0,x1,y0,y1 in product(range(-3,4),repeat=4):
            self.assertEqual(
                add(x1,y1)-add(x1,y0)-add(x0,y1)+add(x0,y0),0
            )

    def test_thresholded_additive_pair_only_no_logit_interaction(self):
        outputs=[int(add(x,y)>=2) for x,y in ((0,0),(1,0),(0,1),(1,1))]
        self.assertEqual(outputs,[0,0,0,1])
        self.assertEqual(add(1,1)-add(1,0)-add(0,1)+add(0,0),0)

    def test_nonlinear_and_pair_only_with_logit_interaction(self):
        outputs=[int(mul(x,y)>=1) for x,y in ((0,0),(1,0),(0,1),(1,1))]
        self.assertEqual(outputs,[0,0,0,1])
        self.assertEqual(mul(1,1)-mul(1,0)-mul(0,1)+mul(0,0),1)


if __name__ == "__main__":
    unittest.main()

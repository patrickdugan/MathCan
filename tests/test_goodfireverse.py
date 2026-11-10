import itertools
import unittest
from fractions import Fraction as F
from research.goodfireverse.gram_holonomy import (
    triangle_gram, determinant3, positive_definite3,
    pairwise_projector_overlaps, triple_projector_trace,
    rank_one_loop_sign, gauge_flip, multiply2, transpose2,
    rotation, matrix_loop, gauge_transport)


class HolonomyTests(unittest.TestCase):
    def test_equal_pairwise_data_opposite_loop_sign(self):
        plus, minus = triangle_gram(1), triangle_gram(-1)
        self.assertTrue(positive_definite3(plus))
        self.assertTrue(positive_definite3(minus))
        self.assertEqual(determinant3(plus), F(27, 32))
        self.assertEqual(determinant3(minus), F(25, 32))
        self.assertEqual(pairwise_projector_overlaps(plus),
                         pairwise_projector_overlaps(minus))
        self.assertEqual(pairwise_projector_overlaps(plus), (F(1, 16),)*3)
        self.assertEqual(triple_projector_trace(plus), F(1, 64))
        self.assertEqual(triple_projector_trace(minus), F(-1, 64))
        self.assertEqual(rank_one_loop_sign(plus), 1)
        self.assertEqual(rank_one_loop_sign(minus), -1)

    def test_all_local_frame_sign_choices(self):
        for orientation in (1, -1):
            m = triangle_gram(orientation)
            for signs in itertools.product((-1, 1), repeat=3):
                flipped = gauge_flip(m, signs)
                self.assertEqual(pairwise_projector_overlaps(flipped),
                                 pairwise_projector_overlaps(m))
                self.assertEqual(triple_projector_trace(flipped),
                                 triple_projector_trace(m))
                self.assertEqual(rank_one_loop_sign(flipped),
                                 rank_one_loop_sign(m))

    def test_rank_two_gauge_covariance_exact(self):
        R1 = rotation(F(3, 5), F(4, 5))
        R2 = rotation(F(5, 13), F(12, 13))
        refl = ((F(1), F(0)), (F(0), F(-1)))
        edges = (R1, refl, R2)
        gauges = (refl, R2, R1)
        transformed = tuple(gauge_transport(edges[k], gauges[k],
                                            gauges[(k+1) % 3])
                            for k in range(3))
        raw_loop = matrix_loop(edges)
        gauged_loop = matrix_loop(transformed)
        expected = multiply2(multiply2(transpose2(gauges[0]), raw_loop), gauges[0])
        self.assertEqual(gauged_loop, expected)
        self.assertNotEqual(raw_loop, gauged_loop)


if __name__ == '__main__':
    unittest.main()

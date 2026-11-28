"""NRF-10 exact finite rational projector Gram and drift oracle."""
from fractions import Fraction as Q
from random import Random
import unittest
from research.compactification.projector_leakage_geometry import (
    mat, identity, gram_dark_squared, gram_shear_squared,
    projector_from_circle, full_motion_bound_squared, jensen_gap
)

class ProjectorLeakageTests(unittest.TestCase):
    def test_rational_gram_and_motion_1200(self):
        g = Random(1010)
        for _ in range(1200):
            t=Q(g.randint(-8,8),g.randint(1,11))
            s=Q(g.randint(-8,8),g.randint(1,11))
            P,R=projector_from_circle(t),projector_from_circle(s)
            J=mat([[Q(g.randint(-11,11),13) for j in range(2)] for i in range(2)])
            gram_dark_squared(P,J)
            actual,bound=full_motion_bound_squared(P,R,J)
            self.assertLessEqual(actual,bound)

    def test_462_exact_jordan_shears(self):
        count=0
        for b in (Q(-3),Q(-1,2),Q(0),Q(5,6),Q(2),Q(7)):
            for i in range(-38,39):
                gram_shear_squared(b,Q(i,11))
                count+=1
        self.assertEqual(count,462)

    def test_3d_coordinates(self):
        P=mat([[1,0,0],[0,0,0],[0,0,0]])
        R=mat([[0,0,0],[0,1,0],[0,0,0]])
        J=mat([[3,4,5],[-2,0,7],[9,-3,1]])
        self.assertEqual(gram_dark_squared(P,J),Q(41))
        a,b=full_motion_bound_squared(P,R,J)
        self.assertLessEqual(a,b)

    def test_jensen_exact(self):
        self.assertGreater(jensen_gap([Q(0),Q(1,3),Q(3,4),Q(5,6)]),0)
        self.assertEqual(jensen_gap([Q(3,4)]*12),0)
        with self.assertRaises(ValueError):jensen_gap([])
        with self.assertRaises(ValueError):jensen_gap([-1,2])

    def test_nonorthogonal_projection_rejected(self):
        with self.assertRaises(ValueError):
            gram_dark_squared(mat([[1,1],[0,1]]),identity(2))

if __name__=="__main__":
    unittest.main()

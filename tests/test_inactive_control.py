"""OLM-17 exact Fraction rank, sham feasibility and residual tests."""
import sys
import unittest
from pathlib import Path
from fractions import Fraction as Q
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"research"/"orbit_lock"))
import inactive_control as m


class InactiveControlOracle(unittest.TestCase):
    def test_small_d_rank_and_nullspace(self):
        for d in range(3,7):
            A=tuple(m.e(i,d) for i in range(min(d,4)))
            self.assertEqual(m.rank(A,d),len(A))
            ns=m.nullspace(A,d)
            self.assertEqual(len(ns),d-len(A))
            self.assertTrue(all(m.mv(A,x)==(Q(0),)*len(A) for x in ns))

    def test_unavoidable_inactive_displacement(self):
        d=5
        A=tuple(m.e(i,d) for i in range(4))
        B=tuple(m.e(i,d) for i in range(d))
        delta=m.e(3,d)
        self.assertEqual(m.residual_floor_sq(A,B,delta),Q(1))
        self.assertFalse(m.exact_matched_sham(A,B,delta)["exact"])
        for sham in (m.e(4,d),tuple(-a for a in m.e(4,d))):
            self.assertEqual(m.norm2(tuple(x-y for x,y in zip(delta,sham))),Q(2))

    def test_low_rank_inactive_conflation_permits_exact_control(self):
        A=tuple(m.e(i,5) for i in range(4))
        B=(tuple(a+b for a,b in zip(m.e(3,5),m.e(4,5))),)
        result=m.exact_matched_sham(A,B,m.e(3,5))
        self.assertEqual(result["sham"],m.e(4,5))
        self.assertTrue(result["exact"])
        self.assertTrue(result["equal_dose_exact"])
        self.assertEqual(m.residual_floor_sq(A,B,m.e(3,5)),Q(0))

    def test_exact_matching_may_fail_equal_dose(self):
        A=tuple(m.e(i,5) for i in range(4))
        B=(m.e(4,5),)
        result=m.exact_matched_sham(A,B,m.e(3,5))
        self.assertTrue(result["exact"])
        self.assertEqual(result["minimum_sqnorm"],0)
        self.assertEqual(result["nullity"],0)
        self.assertFalse(result["equal_dose_exact"])

    def test_extra_null_direction_recovers_equal_dose(self):
        A=tuple(m.e(i,6) for i in range(4))
        B=(m.e(4,6),)
        result=m.exact_matched_sham(A,B,m.e(3,6))
        self.assertTrue(result["exact"])
        self.assertEqual(result["nullity"],1)
        self.assertTrue(result["equal_dose_exact"])
        self.assertEqual(m.residual_floor_sq(A,B,m.e(3,6)),Q(0))

    def test_dimension_four_no_nonzero_tangent_sham(self):
        A=tuple(m.e(i,4) for i in range(4))
        self.assertEqual(m.nullspace(A,4),())
        self.assertFalse(m.exact_matched_sham(A,(),m.e(3,4))["equal_dose_exact"])

    def test_gradient_nuisance_bound_attains_linear_limit(self):
        # m(h)=b·h, b=e4; target coefficient alpha=0 and B=e4.
        # Delta=e4, tangent sham=e5 give D=1 and epsilon=1; G=1, E=M=0.
        d=5
        B=(m.e(3,d),)
        delta=m.e(3,d);sham=m.e(4,d)
        eps2=m.norm2(tuple(x-y for x,y in zip(m.mv(B,delta),m.mv(B,sham))))
        D=m.dot(B[0],tuple(x-y for x,y in zip(delta,sham)))
        self.assertEqual(eps2,Q(1))
        self.assertEqual(D,Q(1))

    def test_rational_dependent_rows_and_consistency(self):
        A=(m.e(0,5),m.e(1,5),m.e(2,5),m.e(3,5))
        B=(m.e(3,5),m.e(3,5))
        self.assertEqual(m.residual_floor_sq(A,B,m.e(3,5)),Q(2))
        self.assertFalse(m.exact_matched_sham(A,B,m.e(3,5))["exact"])


if __name__=="__main__":
    unittest.main()

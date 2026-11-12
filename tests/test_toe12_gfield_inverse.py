"""TOE-12 exact matrix resolvent and auxiliary G2-form elimination."""
from fractions import Fraction as F
from random import Random
import unittest

from research.toe.gfield_linearization import (
    response_first,exact_resolvent,trial_response,reference_example,
)
from research.toe.jordan_principal import eye,zero,add,mm
from research.toe.operator_principal import inverse

class AuxiliaryInverseTests(unittest.TestCase):
    def setUp(self):
        self.theta,self.d=trial_response()

    def test_full_six_dimensional_nontrivial_variation(self):
        v=response_first(self.theta,self.d)
        self.assertTrue(any(x for row in v for x in row))
        self.assertEqual(len(v),6)

    def test_variation_satisfies_linearized_inverse_constraint(self):
        g=inverse(self.theta)
        dg=response_first(self.theta,self.d)
        self.assertEqual(add(mm(self.theta,dg),mm(self.d,g)),zero(6))
        self.assertEqual(add(mm(dg,self.theta),mm(g,self.d)),zero(6))

    def test_exact_second_order_resolvent(self):
        for t in (F(1,100),F(1,1000),F(-1,1000)):
            self.assertTrue(exact_resolvent(self.theta,self.d,t)['resolvent_quadratic_identity'])

    def test_scalar_direction_commuting_special_case(self):
        t=tuple(tuple(F(2 if i==j else 0) for j in range(6)) for i in range(6))
        d=tuple(tuple(F(3 if i==j else 0) for j in range(6)) for i in range(6))
        self.assertEqual(response_first(t,d),tuple(tuple(F(-3,4) if i==j else F() for j in range(6)) for i in range(6)))

    def test_pure_gauge_zero_delta_G(self):
        self.assertEqual(response_first(self.theta,zero(6)),zero(6))

    def test_inverse_resolvent_convergence(self):
        norms=[]
        for t in (F(1,1000),F(1,10000),F(1,100000)):
            rem=exact_resolvent(self.theta,self.d,t)['second_order_remainder']
            norms.append(sum((abs(x) for row in rem for x in row),F()))
        self.assertGreater(norms[0],norms[1]);self.assertGreater(norms[1],norms[2])

    def test_noncommuting_rational_perturbations(self):
        rng=Random(1803)
        for _ in range(25):
            a=[[F(0) for _ in range(6)] for _ in range(6)]
            for j in range(6):a[j][j]=F(rng.randint(2,8),2)
            d=[[F(rng.randint(-2,2),20) for k in range(6)] for j in range(6)]
            r=exact_resolvent(tuple(map(tuple,a)),tuple(map(tuple,d)),F(1,100))
            self.assertTrue(r['resolvent_quadratic_identity'])

    def test_invalid_matrix_rejected(self):
        with self.assertRaises(ValueError):response_first(((1,),),((1,),))
        with self.assertRaises(ValueError):exact_resolvent(self.theta,self.d,0)

    def test_reference_is_conditional(self):
        r=reference_example()
        self.assertGreater(r['nonzero_first_variation_entries'],0)
        self.assertFalse(r['full_Gfield_and_metric_equations_verified'])

if __name__=='__main__':unittest.main()

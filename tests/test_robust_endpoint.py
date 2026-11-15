"""OLM-10 exact endpoint neighborhood certificates (stdlib only)."""
import unittest
from fractions import Fraction as Q
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import robust_endpoint as m


class RobustEndpointTests(unittest.TestCase):
    def test_exact_euclidean_ball_containment_with_anisotropic_vectors(self):
        h=(Q(1,3),Q(2,3),Q(-1,4))
        u=(Q(1),0,0)
        v=(0,Q(1),0)
        anchor_error=(Q(0),Q(1,32),Q(0))
        u_error=(Q(1,64),Q(0),Q(0))
        v_error=(Q(0),Q(-1,64),Q(0))
        a=tuple(x+y for x,y in zip(h,anchor_error))
        up=tuple(x+y for x,y in zip(u,u_error))
        vp=tuple(x+y for x,y in zip(v,v_error))
        self.assertTrue(m.containment_witness(h,u,v,Q(1,5),Q(1,32),Q(1,64),Q(1,64),a,up,vp))
        with self.assertRaises(ValueError):
            m.containment_witness(h,u,v,Q(1,5),Q(1,64),Q(1,64),Q(1,64),a,up,vp)

    def test_equal_norm_box_certificates_survive_small_uncertainty(self):
        W=((Q(2),0),(0,Q(1)))
        for delta in (Q(0),Q(1,1000),Q(1,100)):
            result=m.robust_linear_comparison((0,0),(1,0),(0,1),Q(1,5),delta,delta,delta,W)
            self.assertEqual(result['status'],'active_greater')
        result=m.robust_linear_comparison((0,0),(1,0),(0,1),Q(1,5),Q(1,2),Q(1,2),Q(1,2),W)
        self.assertEqual(result['status'],'inconclusive')

    def test_outward_perturbation_box_inclusion_and_monotonicity(self):
        a=m.input_boxes((Q(1),Q(2)),(1,0),(0,1),Q(1,5),Q(1,1000),Q(1,1000),Q(1,1000))
        b=m.input_boxes((Q(1),Q(2)),(1,0),(0,1),Q(1,5),Q(1,500),Q(1,500),Q(1,500))
        self.assertTrue(m.contains_all_boxes(b,a))
        self.assertFalse(m.contains_all_boxes(a,b))
        self.assertEqual(a['active'][0][0],Q(1)+Q(1,5)-Q(6,5000))

    def test_relative_raw_uncertainty_normalization_bound(self):
        for rho in (Q(0),Q(1,100),Q(1,10),Q(1,4)):
            v=m.raw_to_unit_direction_error(rho)
            self.assertGreaterEqual(v,2*rho)
        with self.assertRaises(ValueError): m.raw_to_unit_direction_error(1)
        with self.assertRaises(ValueError): m.raw_to_unit_direction_error(-1)

    def test_exact_square_interval_and_ordering_ties(self):
        self.assertEqual(m.square((Q(-2),Q(3))),(Q(0),Q(9)))
        self.assertEqual(m.square((Q(-3),Q(-2))),(Q(4),Q(9)))
        self.assertEqual(m.squared_effect(((Q(-1),Q(1)),),((Q(0),Q(0)),)),(Q(0),Q(1)))
        with self.assertRaises(ValueError):m.input_boxes((1,),(1,),(1,),0,0,0,0)
        with self.assertRaises(ValueError):m.linear_forward(((0,1),),((1,2),))


if __name__=='__main__':
    unittest.main()

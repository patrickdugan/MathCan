"""OLM-12 exact conic/angular radius and sharp adversarial witness tests."""
import sys
from pathlib import Path
from fractions import Fraction as Q
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"research"/"orbit_lock"))
import conic_self_selection as c


class SelfSelectionConeTests(unittest.TestCase):
    def setUp(self):
        self.normals=((Q(1),Q(0)),(Q(0),Q(1)),(Q(-1),Q(0)))
        self.ray=(Q(2),Q(1))
        self.top=c.cone_certificate(self.normals,(0,),self.ray)

    def test_exact_sharp_raw_and_spherical_margins(self):
        x=self.top
        self.assertEqual(x['status'],'interior')
        self.assertTrue(x['all_positive_ray_amplitudes_preserve_selected_set'])
        self.assertEqual(x['minimal_normalized_slope_squared'],Q(1,10))
        self.assertEqual(x['limiting_constraint'],('competitor',0,1))
        self.assertEqual(x['nontrivial_constraints'],3)
        self.assertTrue(c.relative_raw_guard(x,Q(3,10)))
        self.assertFalse(c.relative_raw_guard(x,Q(1,3)))
        self.assertTrue(c.unit_chord_guard(x,Q(3,10)))
        self.assertFalse(c.unit_chord_guard(x,Q(1,3)))
        self.assertTrue(c.joint_normal_and_decoder_guard(x,Q(1,5),Q(1,20)))
        self.assertFalse(c.joint_normal_and_decoder_guard(x,Q(1,5),Q(1,10)))

    def test_boundary_adversary_is_exact_and_sharp(self):
        p=c.sharp_boundary_adversary(self.normals,(0,),self.ray,self.top)
        self.assertEqual(p['relative_raw_boundary_distance_squared'],Q(1,10))
        self.assertEqual(p['exact_boundary_ray'],(Q(3,2),Q(3,2)))
        self.assertEqual(p['boundary_gap_slope'],Q(0))
        self.assertLess(p['outside_gap_slope'],Q(0))
        projected=c.cone_certificate(self.normals,(0,),p['exact_boundary_ray'])
        crossed=c.cone_certificate(self.normals,(0,),p['exact_overshoot_ray'])
        self.assertEqual(projected['status'],'boundary')
        self.assertEqual(crossed['status'],'outside')
        self.assertTrue(c.relative_raw_guard(projected,0))
        self.assertFalse(c.relative_raw_guard(projected,Q(1,10)))

    def test_different_selected_support_cone_and_boundary_cases(self):
        x=c.cone_certificate(self.normals,(0,1),self.ray)
        self.assertEqual(x['status'],'interior')
        self.assertEqual(x['minimal_normalized_slope_squared'],Q(1,5))
        self.assertEqual(c.cone_certificate(self.normals,(0,),(Q(-1),0))['status'],'outside')
        self.assertEqual(c.cone_certificate(self.normals,(0,),(Q(0),Q(-1)))['status'],'boundary')
        whole=c.cone_certificate(((0,0),(0,0)),(0,),(1,0))
        self.assertEqual(whole['status'],'unconstrained')
        self.assertTrue(c.relative_raw_guard(whole,1000000))
        self.assertTrue(c.unit_chord_guard(whole,1000000))

    def test_rational_sqrt_and_exact_chord_threshold(self):
        for q in (Q(0),Q(1,10),Q(2,7),Q(1)):
            lo,hi=c.dyadic_sqrt_bracket(q,64)
            self.assertLessEqual(lo*lo,q)
            self.assertGreaterEqual(hi*hi,q)
            self.assertLessEqual(hi-lo,Q(1,1<<64))
        q2=self.top['minimal_normalized_slope_squared']
        # chord squared = 2 - 2 sqrt(1-q²); exact boundary equality:
        # q² == x-x²/4, so guard is strict for x below the root.
        self.assertEqual(q2,Q(1,10))
        self.assertTrue(c.unit_chord_guard(self.top,Q(1,4)))
        self.assertFalse(c.unit_chord_guard(self.top,Q(1,2)))
        self.assertFalse(c.unit_chord_guard(self.top,Q(2)))
        self.assertEqual(c.dot((Q(1,3),Q(2,3)),(3,6)),Q(5))

    def test_normalization_uses_physical_hidden_units(self):
        original=((Q(2),Q(0)),(Q(0),Q(6)),(Q(-3),Q(0)))
        scaled=c.physical_encoder_normals(original,(Q(2),Q(3)))
        self.assertEqual(scaled,((Q(1),Q(0)),(Q(0),Q(2)),(Q(-3,2),Q(0))))
        ordinary=c.cone_certificate(original,(0,),(2,1))
        physical=c.cone_certificate(scaled,(0,),(2,1))
        self.assertNotEqual(ordinary['minimal_normalized_slope_squared'],
                            physical['minimal_normalized_slope_squared'])

    def test_invalid_input_abstains(self):
        with self.assertRaises(ValueError):c.physical_encoder_normals((),(1,))
        with self.assertRaises(ValueError):c.physical_encoder_normals(((1,2),),(1,0))
        with self.assertRaises(ValueError):c.cone_certificate(self.normals,(0,),(0,0))
        with self.assertRaises(ValueError):c.cone_certificate(self.normals,(0,1,2),(1,0))
        with self.assertRaises(ValueError):c.relative_raw_guard(self.top,-1)
        with self.assertRaises(ValueError):c.unit_chord_guard(self.top,-1)
        with self.assertRaises(ValueError):c.joint_normal_and_decoder_guard(self.top,-1,0)
        with self.assertRaises(ValueError):
            c.sharp_boundary_adversary(self.normals,(0,),self.ray,self.top,0)
        with self.assertRaises(ValueError):c.dyadic_sqrt_bracket(Q(-1))

if __name__=="__main__":
    unittest.main()

"""Ten exact rational tests for OLM-20 anchored gradient math."""
import unittest
from fractions import Fraction as F
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import anchored_gradient_refit as m


class OLM20WitnessTests(unittest.TestCase):
    def test_sharp_difference_sensitive_bound_rational(self):
        for r in (F(1,10),F(3,5),F(11,4)):
            x=m.sharp_quadratic(F(7),r)
            self.assertEqual(x['error'],x['sharp_bound'])
            self.assertEqual(x['error'],F(7)*r*r/2)

    def test_identical_edits_have_zero_anchored_prediction_error(self):
        h=m.vec((1,2));a=m.vec((F(2,3),F(7,5)))
        f=lambda x:F(10)+x[0]*x[0]+3*x[1]*x[1]
        Ea=m.finite_erase(f,h,a)
        g=m.vec((2,12))
        self.assertEqual(m.anchored_predict(Ea,g,a,a),Ea)

    def test_linear_dose_example_exact_gradient_transport(self):
        x=m.linear_dose_witness()
        self.assertEqual(x['source_effect'],3)
        self.assertEqual(x['target_effect'],6)
        self.assertEqual(x['anchored_predicted_target'],6)
        self.assertEqual(x['reference_dose_squared'],1)
        self.assertEqual(x['target_dose_squared'],4)

    def test_clean_positive_and_reversed_target_effect_near_boundary(self):
        x=m.reversed_sign_witness()
        self.assertGreater(x['clean_margin'],0)
        self.assertGreater(x['edited_target_margin'],0)
        self.assertEqual(x['predicted_effect'],1)
        self.assertEqual(x['target_effect'],-1)
        self.assertEqual(x['remainder_abs'],x['sharp_bound'])
        self.assertFalse(x['strict_sign_certificate_holds'])

    def test_exact_orthogonal_conjugacy_for_anchored_predictor(self):
        x=m.orthogonal_witness()
        self.assertEqual(x['source_effect'],x['transported_source_effect'])
        self.assertEqual(x['target_effect'],x['transported_target_effect'])
        self.assertEqual(x['anchored_prediction'],x['transported_prediction'])

    def test_orthogonal_gauge_preserves_difference_and_gradient_norms(self):
        x=m.orthogonal_witness()
        self.assertEqual(x['original_edit_sq_distance'],x['rotated_edit_sq_distance'])
        self.assertEqual(x['original_gradient_sq_norm'],x['rotated_gradient_sq_norm'])

    def test_norm_matched_distinct_directions(self):
        x=m.equal_dose_norm_witness()
        self.assertEqual(x['norm_A_sq'],x['norm_B_sq'])
        self.assertEqual(x['edit_distance_sq'],F(4,5))
        self.assertEqual(x['angle_dot'],F(3,5))

    def test_row_basis_is_exactly_orthogonal(self):
        q=m.Q;t=m.trans(q)
        self.assertEqual(m.rowmat(m.rowmat(m.vec((1,0)),q),t),m.vec((1,0)))
        self.assertEqual(m.rowmat(m.rowmat(m.vec((0,1)),q),t),m.vec((0,1)))

    def test_sign_certificate_on_linear_refit_is_valid(self):
        x=m.linear_dose_witness()
        # Hessian = 0, so anchored prediction equals exact refit effect.
        self.assertEqual(x['anchored_predicted_target'],x['target_effect'])
        self.assertGreater(abs(x['anchored_predicted_target']),0)

    def test_guard_invalid_scales_and_vector_shapes(self):
        with self.assertRaises(ValueError):m.sharp_quadratic(-1,1)
        with self.assertRaises(ValueError):m.sharp_quadratic(1,0)
        with self.assertRaises(ValueError):m.dot((1,),(1,2))
        with self.assertRaises(ValueError):m.rowmat((1,2,3),m.Q)


    def test_reference_causal_anchor_can_hurt_vs_direct_gradient(self):
        r=m.anchor_direct_competition(F(1),F(1,2))
        self.assertEqual(r['E_source'],-1)
        self.assertEqual(r['E_target'],0)
        self.assertEqual(r['direct_absolute_error'],F(1,2))
        self.assertEqual(r['anchored_absolute_error'],F(3,2))
        self.assertGreater(r['criterion_polynomial'],0)
        self.assertFalse(r['anchor_better'])
        self.assertGreater(r['target_erased_margin'],0)

    def test_matching_finite_residuals_support_anchored_improvement(self):
        r=m.anchor_direct_competition(F(1,2),F(3,4))
        self.assertEqual(r['E_target'],F(-3,8))
        self.assertEqual(r['anchored_prediction'],F(1,4))
        self.assertEqual(r['anchored_absolute_error'],F(5,8))
        self.assertEqual(r['direct_absolute_error'],F(9,8))
        self.assertLess(r['criterion_polynomial'],0)
        self.assertTrue(r['anchor_better'])

    def test_exact_anchored_minus_direct_is_source_finite_residual(self):
        for a,b in ((F(1),F(1,2)),(F(1,2),F(3,4)),(F(1,3),F(2,3))):
            r=m.anchor_direct_competition(a,b)
            self.assertEqual(r['anchored_prediction']-r['direct_clean_gradient_prediction'],
                             r['source_finite_residual'])
            self.assertEqual(r['E_target']-r['direct_clean_gradient_prediction'],
                             r['target_finite_residual'])
            self.assertEqual(r['anchored_absolute_error']**2-r['direct_absolute_error']**2,
                             r['criterion_polynomial'])



if __name__=='__main__':unittest.main()

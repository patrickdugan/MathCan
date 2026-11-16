"""Ten stdlib exact-Fraction checks for OLM-19 gauge and refit aliases."""
import sys
import unittest
from pathlib import Path
from fractions import Fraction as Q
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import sae_gauge_refit as m


class GaugeRefitTests(unittest.TestCase):
    def test_exact_rational_dense_orthogonal_transport(self):
        e1=m.vec((1,0));e2=m.vec((0,1))
        qt=m.transpose(m.Q_ROT)
        self.assertEqual(m.rowmul(m.rowmul(e1,m.Q_ROT),qt),e1)
        self.assertEqual(m.rowmul(m.rowmul(e2,m.Q_ROT),qt),e2)

    def test_nonlinear_recurrent_conjugacy_multiple_visits(self):
        for steps in (0,1,2,3,5):
            result=m.orthogonal_transport_witness(steps)
            self.assertTrue(result['hidden_transport_identical'])
            self.assertTrue(result['finite_effect_identical'])
            self.assertEqual(result['source_edit_sq_norm'],
                             result['transported_edit_sq_norm'])

    def test_same_matched_activation_and_zero_reconstruction_error(self):
        for x,y in ((Q(1),Q(1)),(Q(1,4),Q(3,2)),(Q(5),Q(7,3))):
            result=m.sae_refit_alias_witness(x,y)
            self.assertTrue(result['matched_atom_two_activations_equal'])
            self.assertEqual(result['clean_state'],result['reference_reconstruction'])
            self.assertEqual(result['clean_state'],result['refit_reconstruction'])

    def test_opposite_native_causal_effect_in_same_frozen_task(self):
        result=m.sae_refit_alias_witness()
        self.assertEqual(result['common_clean_margin'],Q(13))
        self.assertEqual(result['native_erasure_drop_A'],Q(1))
        self.assertEqual(result['native_erasure_drop_B'],Q(-1))
        self.assertEqual(result['erased_A'],m.vec((1,0)))
        self.assertEqual(result['erased_B'],m.vec((2,0)))

    def test_matched_decoder_rays_are_distinct(self):
        row=m.sae_refit_alias_witness()
        self.assertNotEqual(row['reference_decoder_two'],row['refit_decoder_two'])
        self.assertEqual(row['reference_code'][1],row['refit_code'][1])

    def test_physical_edit_lipschitz_constant_is_sharp(self):
        row=m.sharp_physical_stability_bound()
        self.assertEqual(row['absolute_drop_difference'],Q(5))
        self.assertEqual(row['edit_distance_sq'],Q(1))
        self.assertEqual(row['absolute_drop_difference']**2,
                         row['squared_stability_ceiling'])

    def test_strict_bound_forces_causal_sign_stability(self):
        row=m.sign_stability_witness()
        self.assertTrue(row['same_positive_sign'])
        self.assertEqual(row['effect_A'],Q(3))
        self.assertEqual(row['effect_B'],Q(17,5))
        self.assertGreater(row['source_sq_effect'],row['bound_squared'])

    def test_equal_norm_decoder_angle_identity(self):
        row=m.equal_dose_angle_witness()
        self.assertEqual(row['dose_squared_A'],1)
        self.assertEqual(row['dose_squared_B'],1)
        self.assertEqual(row['cosine'],Q(3,5))
        self.assertEqual(row['physical_edit_distance_squared'],Q(4,5))
        self.assertEqual(row['physical_edit_distance_squared'],
                         row['angle_identity_squared'])

    def test_physical_gauge_code_and_reconstruction_are_separate(self):
        # Reconstruction alias changes physical erased states despite exact code two.
        x=m.sae_refit_alias_witness(Q(2),Q(3))
        self.assertEqual(x['reference_code'][1],x['refit_code'][1])
        self.assertEqual(x['native_erasure_drop_A'],Q(3))
        self.assertEqual(x['native_erasure_drop_B'],Q(-3))

    def test_dimension_and_cell_guards_fail_closed(self):
        with self.assertRaises(ValueError):m.rowmul((1,2,3),m.Q_ROT)
        with self.assertRaises(ValueError):m.dot((1,),(1,2))
        with self.assertRaises(ValueError):m.sae_refit_alias_witness(0,1)
        with self.assertRaises(ValueError):m.orthogonal_transport_witness(-1)


if __name__=="__main__":unittest.main()

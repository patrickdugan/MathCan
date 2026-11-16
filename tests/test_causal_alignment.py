"""OLM-14 exact witnesses for causal nonidentifiability and transfer tests."""
import sys
import unittest
from pathlib import Path
from fractions import Fraction as Q
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import causal_alignment as m


class CausalAlignmentTests(unittest.TestCase):
    def test_identical_activation_and_clean_classification_opposite_causal_signs(self):
        out=m.causal_nonidentifiability_witness()
        self.assertTrue(out['identical_correct_predictions'])
        self.assertEqual(out['A_causal_response'],Q(1))
        self.assertEqual(out['B_causal_response'],Q(-1))
        self.assertTrue(all(z>0 for z in out['teacher_A_margins']))
        self.assertTrue(all(z>0 for z in out['teacher_B_margins']))

    def test_puzzle_nuisance_and_positive_scale_invariance(self):
        a=(Q(1,3),Q(1,2),Q(7,5),Q(-1,4))
        b=(Q(2),Q(4),Q(3),Q(-2))
        orig=m.squared_centered_cosine(a,b)
        shifted=m.squared_centered_cosine(
            [Q(7)*x+100 for x in a],
            [Q(13)*y-70 for y in b])
        self.assertEqual(orig,shifted)
        self.assertEqual(orig['status'],'identified')
        inverted=m.squared_centered_cosine(a,[-z for z in b])
        self.assertEqual(orig['cosine_squared'],inverted['cosine_squared'])
        self.assertEqual(orig['sign'],-inverted['sign'])

    def test_calibration_sign_only_changes_with_calibration_vectors(self):
        pairs=[((1,2,3),(3,2,1)),((2,3,4),(4,3,2))]
        self.assertEqual(m.calibration_sign(pairs),-1)
        x=[((1,2,3),(1,2,3))]
        self.assertEqual(m.calibration_sign(x),1)
        self.assertEqual(m.calibration_sign([((1,1,1),(2,2,2))]),1)

    def test_finite_response_curvature_and_isometric_conjugacy(self):
        for r in (Q(1,100),Q(1,5),Q(4,5)):
            x=m.finite_difference_transfer_witness(r)
            self.assertEqual(x['transfer_error'],r*r)
            self.assertGreaterEqual(x['rigorous_transfer_upper'],x['transfer_error'])
            f=m.isometric_conjugacy_witness(r)
            self.assertTrue(f['exact_conjugacy'])
            self.assertEqual(f['target_response'],f['source_response']*f['signed_scale'])

    def test_fail_closed_on_unidentified_zero_variance_and_input_errors(self):
        self.assertEqual(m.squared_centered_cosine((1,1,1),(2,3,4))['status'],
                         'abstain_zero_centered_variance')
        for args in (((1,), (1,)), ((1,2), (1,2,3))):
            with self.assertRaises(ValueError):m.squared_centered_cosine(*args)
        with self.assertRaises(ValueError):m.calibration_sign([])
        with self.assertRaises(ValueError):
            m.symmetric_difference(lambda x:x,0,1,0)
        with self.assertRaises(ValueError):
            m.isometric_conjugacy_witness(-1)


if __name__=='__main__':
    unittest.main()

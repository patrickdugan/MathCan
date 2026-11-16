"""Ten rational exact tests for OLM-22 LAD residual transfer."""
import unittest,sys
from pathlib import Path
from fractions import Fraction as F
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import weighted_median_transfer as w


class WitnessTests(unittest.TestCase):
    def test_weighted_median_handles_signed_residual_covariate(self):
        rows=[(0,0,-2,2),(0,1,1,1),(1,0,4,8)]
        beta=w.weighted_median_lad(rows)
        self.assertEqual(beta,2)
        self.assertLessEqual(w.mae(rows,beta),w.mae(rows,F(0)))

    def test_calibration_lad_beats_original_ridge(self):
        r=w.calibration_failure_example()
        self.assertEqual(r['lad'],0)
        self.assertEqual(r['ridge'],F(4,7))
        self.assertEqual(r['cal_LAD_MAE'],F(3,5))
        self.assertEqual(r['cal_ridge_MAE'],F(29,35))

    def test_target_shift_can_reverse_lad_advantage(self):
        r=w.calibration_failure_example()
        self.assertTrue(r['same_source_marginal'])
        self.assertEqual(r['test_LAD_MAE'],2)
        self.assertEqual(r['test_ridge_MAE'],F(10,7))
        self.assertGreater(r['test_LAD_MAE'],r['test_ridge_MAE'])

    def test_lower_weighted_median_tie_rule(self):
        r=w.lower_median_tie_example()
        self.assertEqual(r['lad'],0)
        self.assertEqual(r['zero_loss'],r['two_loss'])
        self.assertEqual(r['one_loss'],r['zero_loss'])

    def test_heavy_weight_overrides_unweighted_median(self):
        rows=[(1,1,10,20),(1,2,1,-2),(1,3,1,-3)]
        self.assertEqual(w.weighted_median_lad(rows),2)

    def test_exact_symmetric_clip(self):
        self.assertEqual(w.weighted_median_lad([(0,0,1,9)]),2)
        self.assertEqual(w.weighted_median_lad([(0,0,1,-9)]),-2)

    def test_zero_source_covariates_contribute_constant_only(self):
        rows=[(0,0,0,1000),(0,1,1,F(1,2))]
        self.assertEqual(w.weighted_median_lad(rows),F(1,2))

    def test_coupled_absolute_loss_shift_bound(self):
        xs=[(F(1),F(2),F(3),F(4)),(F(-1),F(0),F(1),F(0))]
        for beta in (-2,0,F(1,3),2):
            r=w.finite_coupling_bound(xs,beta)
            self.assertLessEqual(r['absolute_risk_shift'],r['coupled_l1_bound'])

    def test_coupled_lipschitz_2_constant_is_sharp(self):
        r=w.sharp_coupling_example()
        self.assertEqual(r['absolute_risk_shift'],F(6,5))
        self.assertEqual(r['absolute_risk_shift'],r['coupled_l1_bound'])

    def test_invalid_weight_and_beta_guards(self):
        with self.assertRaises(ValueError):w.weighted_median_lad([(0,0,0,1)])
        with self.assertRaises(ValueError):w.weighted_median_lad([])
        with self.assertRaises(ValueError):w.finite_coupling_bound([],0)
        with self.assertRaises(ValueError):w.finite_coupling_bound([(0,0,1,2)],3)


if __name__=='__main__':unittest.main()

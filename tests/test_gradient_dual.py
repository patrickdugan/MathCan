"""Eight stdlib exact-Fraction OLM-18 theorem regression tests."""
import sys
import unittest
from pathlib import Path
from fractions import Fraction as Q
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import gradient_dual as g


class GradientDualTests(unittest.TestCase):
    def test_full_rank_inactive_dual_represents_task_gradient_exactly(self):
        row=g.test_dual_witness()
        self.assertEqual(row['reconstructed_gradient'],g.v((2,3)))
        self.assertEqual(row['task_directional'],row['inactive_dual_directional'])
        self.assertEqual(row['task_directional'],Q(1))

    def test_minimum_norm_orthogonal_null_correction(self):
        B=((1,0),(0,1),(1,1))
        lam=g.inactive_dual(B,(2,3))
        # B^T(-1,-1,1)=0. This correction is orthogonal to lambda*.
        null=g.v((-1,-1,1))
        self.assertEqual(g.dot(lam,null),0)
        other=tuple(lam[i]+null[i] for i in range(3))
        self.assertEqual(g.norm_sq(other),g.norm_sq(lam)+g.norm_sq(null))

    def test_inactive_cauchy_bound_is_exact_for_identity(self):
        B=((1,0),(0,1))
        grad=g.v((2,3))
        lam=g.inactive_dual(B,grad)
        shift=g.matvec(B,grad)
        self.assertEqual(g.dot(lam,shift),g.norm_sq(lam))
        self.assertEqual(g.norm_sq(lam)*g.norm_sq(shift),
                         g.dot(lam,shift)**2)

    def test_rank_defect_fails_closed(self):
        with self.assertRaisesRegex(ValueError,'rank'):
            g.inactive_dual(((1,0),(2,0)),(1,1))
        with self.assertRaises(ValueError):
            g.inactive_dual(((1,0),(0,1)),(2,3,4))

    def test_equal_dose_orthogonal_edit_quadratic_bound_is_sharp(self):
        for r in (Q(1,10),Q(2,3),Q(5,4)):
            w=g.quadratic_sharpness(r,Q(7))
            self.assertEqual(abs(w['finite_difference']),w['sharp_bound'])
            self.assertEqual(w['kill_sham_dot'],0)

    def test_equal_dose_cubic_third_remainder_bound_is_sharp(self):
        for r in (Q(1,100),Q(1,5),Q(3,2)):
            w=g.cubic_sharpness(r,Q(5))
            self.assertEqual(abs(w['finite_difference']),w['sharp_bound'])

    def test_same_first_second_jets_have_opposite_finite_effect_signs(self):
        out=g.second_jet_obstruction()
        self.assertGreater(out['clean_margin'],0)
        self.assertEqual(out['finite_A'],Q(1))
        self.assertEqual(out['finite_B'],Q(-2))

    def test_dimension_and_invalid_radius_checks(self):
        with self.assertRaises(ValueError):g.dot((1,2),(1,))
        with self.assertRaises(ValueError):g.linear_solve(((1,2),(2,4)),(1,2))
        with self.assertRaises(ValueError):g.quadratic_sharpness(0,1)
        with self.assertRaises(ValueError):g.cubic_sharpness(0,1)


if __name__=="__main__":unittest.main()

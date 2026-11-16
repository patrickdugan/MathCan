"""Exact Fraction regression tests for OLM-15 native erasure bounds."""
import unittest
from pathlib import Path
from fractions import Fraction as Q
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"research"/"orbit_lock"))
import native_erasure as m


class OLM15NativeErasureTests(unittest.TestCase):
    def test_same_clean_activation_and_every_central_response_opposite_full_erase(self):
        for r in (Q(1,100),Q(1,5),Q(1,2),Q(3)):
            row=m.curvature_obstruction(3,r)
            self.assertEqual(row["clean_margin_A"],row["clean_margin_B"])
            self.assertEqual(row["central_A"],Q(1))
            self.assertEqual(row["central_B"],Q(1))
            self.assertEqual(row["native_drop_A"],Q(1))
            self.assertEqual(row["native_drop_B"],Q(-2))
            self.assertGreater(row["erased_margin_B"],0)

    def test_stable_selection_feedback_gain_is_exact(self):
        self.assertEqual(m.stable_selected_residual(Q(3,2),Q(1)),0)
        self.assertEqual(m.stable_selected_residual(Q(3,2),Q(1,3)),Q(1))
        self.assertEqual(m.stable_selected_residual(Q(3,2),Q(0)),Q(3,2))
        for z,g in ((0,0),(1,Q(3,2)),(1,-1)):
            with self.assertRaises(ValueError):
                m.stable_selected_residual(z,g)

    def test_native_erasure_taylor_bound_sharp_for_quadratics(self):
        for b in (Q(1,3),Q(-7,3),Q(5)):
            row=m.quadratic_sharpness(2,b)
            self.assertEqual(row["difference"],row["bound"])
        self.assertEqual(m.erasure_taylor_bound(2,Q(3,2),4),Q(12))
        self.assertEqual(m.two_teacher_bound(1,2,1,3,1,4,2,2),Q(12))

    def test_active_atom_can_have_zero_margin_drop(self):
        row=m.active_but_unnecessary()
        self.assertEqual(row["clean_activation"],1)
        self.assertEqual(row["margin_drop"],0)

    def test_invalid_inputs_fail_closed(self):
        for args in ((-1,1,1),(1,-1,1),(1,1,-1)):
            with self.assertRaises(ValueError):
                m.erasure_taylor_bound(*args)
        with self.assertRaises(ValueError):
            m.native_drop(lambda x:x, 1,-1,1)
        with self.assertRaises(ValueError):
            m.symmetric_response(lambda x:x,1,0)
        with self.assertRaises(ValueError):
            m.two_teacher_bound(0,1,1,1,1,1,1,-1)


if __name__=="__main__":
    unittest.main()

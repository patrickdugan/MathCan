"""Exact-rational checks for the OLM-16 statements and d<=6 obstructions."""
import sys
import unittest
from pathlib import Path
from fractions import Fraction as Q

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"research"/"orbit_lock"))
import selective_projection as p


def e(i,d=5):
    return tuple(Q(int(j==i)) for j in range(d))


class ExactSelectiveProjection(unittest.TestCase):
    def test_dimension_three_to_six_obstructions(self):
        x=p.small_dimensional_obstructions()
        self.assertFalse(x[3]["kill_possible"])
        self.assertTrue(x[4]["kill_possible"])
        self.assertFalse(x[4]["nonzero_tangent_sham"])
        for d in (5,6):
            self.assertTrue(x[d]["kill_possible"])
            self.assertTrue(x[d]["nonzero_tangent_sham"])

    def test_minimum_norm_and_preserved_other_rows(self):
        o=(e(0),e(1),e(2))
        a=tuple(e(3)[i]+e(0)[i]/2 for i in range(5))
        kill=p.selective_kill(o,a,1,Q(1,4))
        self.assertEqual(kill,Q(5,4)*e(3)[0:0]+(Q(0),Q(0),Q(0),Q(5,4),Q(0)))
        self.assertEqual(p.sqnorm(kill),Q(25,16))
        self.assertTrue(all(p.dot(kill,r)==0 for r in o))
        self.assertEqual(p.dot(kill,a),Q(5,4))
        # Another feasible vector has an independent nullspace component.
        alt=tuple(x+y for x,y in zip(kill,e(4)))
        self.assertGreater(p.sqnorm(alt),p.sqnorm(kill))

    def test_row_rank_and_target_span_obstructions(self):
        with self.assertRaises(ValueError):
            p.project_null((e(0),e(0),e(2)),e(3))
        with self.assertRaises(ValueError):
            p.selective_kill((e(0),e(1),e(2)),e(1),1,Q(1,4))

    def test_cell_preservation_vs_new_inactive_feature(self):
        rows=tuple(e(i) for i in range(5))
        pre=(1,1,1,1,-1)
        self.assertTrue(p.strict_top4(rows,pre,(0,0,0,0,0),(0,1,2,3)))
        sham=(Q(0),Q(0),Q(0),Q(0),Q(-3))
        self.assertTrue(all(p.dot(rows[i],sham)==0 for i in range(4)))
        self.assertEqual(p.preactivations_after(rows,pre,sham)[4],Q(2))
        self.assertFalse(p.strict_top4(rows,pre,sham,(0,1,2,3)))

    def test_sign_reversal_exact_under_identical_encodings(self):
        w=p.sign_reversal_witness()
        self.assertEqual(w["clean_plus"],Q(4))
        self.assertEqual(w["clean_minus"],Q(2))
        self.assertEqual(w["effect_plus"],Q(5,2))
        self.assertEqual(w["effect_minus"],Q(-5,2))
        self.assertEqual(p.sqnorm(w["kill"]),p.sqnorm(w["sham"]))

    def test_sharp_curvature_remainder(self):
        r=Q(5,4); M=Q(3,2)
        h=(Q(0),)*5
        kill=tuple(r*x for x in e(3))
        sham=tuple(r*x for x in e(4))
        m=lambda x:(M/2)*(x[3]*x[3]-x[4]*x[4])
        self.assertEqual(p.difference_from_margins(h,kill,sham,m),-M*r*r)

    def test_inactive_leakage_is_sharp(self):
        kill=p.selective_kill((e(0),e(1),e(2)),e(3),1,Q(1,4))
        self.assertEqual(p.dot(e(3),kill),Q(5,4))
        self.assertEqual(p.dot(e(4),kill),0)
        self.assertEqual(p.dot(tuple(2*x for x in e(3)),kill),Q(5,2))


if __name__=="__main__":
    unittest.main()

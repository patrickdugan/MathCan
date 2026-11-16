"""Independent exact-rational checks for OLM-16 affine selective erasure."""
import unittest
from fractions import Fraction as Q
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import selective_erasure as m


class OLM16ExactGeometryTests(unittest.TestCase):
    def test_minimum_norm_selectivity_and_orthogonal_tangent(self):
        a=(Q(2),Q(1),Q(3))
        other=[(Q(0),Q(1),Q(0))]
        chosen=m.minimum_selective_edit(a,other,Q(1),Q(1,5))
        self.assertEqual(m.dot(a,chosen),Q(6,5))
        self.assertEqual(m.dot(other[0],chosen),0)
        tangent=m.project_off_rows((1,0,-2),[a,*other])
        self.assertEqual(m.dot(a,tangent),0)
        self.assertEqual(m.dot(other[0],tangent),0)
        self.assertNotEqual(m.norm_squared(tangent),0)
        # Any feasible perturbation by a tangent is longer, by Pythagoras.
        alternative=m.add(chosen,tangent)
        self.assertEqual(m.norm_squared(alternative),
                         m.norm_squared(chosen)+m.norm_squared(tangent))

    def test_rank_and_source_feature_obstructions_fail_closed(self):
        with self.assertRaisesRegex(ValueError,'dependent'):
            m.minimum_selective_edit((1,0,0),[(0,1,0),(0,1,0)],1,Q(1,10))
        with self.assertRaisesRegex(ValueError,'span'):
            m.minimum_selective_edit((1,0,0),[(1,0,0)],1,Q(1,10))
        with self.assertRaisesRegex(ValueError,'positive'):
            m.minimum_selective_edit((1,0,0),[(0,1,0)],0,Q(1,10))

    def test_exact_tangent_sham_same_dose_and_affine_invariance(self):
        kill=m.minimum_selective_edit((1,0,0),[(0,1,0)],1,Q(1,5))
        self.assertEqual(kill,(Q(6,5),Q(0),Q(0)))
        sham=m.tangent_sham([(1,0,0),(0,1,0)],(0,0,1),
                            m.norm_squared(kill))
        self.assertEqual(sham,(Q(0),Q(0),Q(6,5)))
        self.assertEqual(m.norm_squared(sham),m.norm_squared(kill))

    def test_sharp_curvature_bound(self):
        for r in (Q(1,100),Q(1,5),Q(7,4)):
            witness=m.sharp_quadratic_witness(r,Q(3))
            self.assertEqual(abs(witness['observed_difference']),Q(3)*r*r)
            self.assertEqual(abs(witness['observed_difference']),witness['curvature_bound'])

    def test_active_feature_task_irrelevance_witness(self):
        x=m.inactive_task_counterexample()
        self.assertEqual(x['clean_selected_activation'],1)
        self.assertEqual(x['task_effect_difference'],0)
        self.assertEqual(m.norm_squared(x['selective_edit']),
                         m.norm_squared(x['tangent_sham']))


if __name__=='__main__':unittest.main()

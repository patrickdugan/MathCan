"""OLM-11: sharp finite polyhedral SAE feature identity tests."""
import sys
from pathlib import Path
from fractions import Fraction as Q
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import selection_cells as c


class SelectionCellTests(unittest.TestCase):
    def test_exact_physical_norm_and_sharp_topk_top1_radii(self):
        rows=((Q(1),),(Q(-1),),(Q(2),))
        offs=(Q(2),Q(1),Q(0))
        cert=c.topk_selection_certificate(rows,offs,(Q(0),),k=2)
        self.assertEqual(cert['top_index'],0)
        self.assertEqual(cert['topk_indices'],(0,1))
        self.assertEqual(cert['top1']['radius_squared'],Q(1,4))
        self.assertEqual(cert['topk']['radius_squared'],Q(1,9))
        self.assertEqual(cert['top1']['active_boundary'],('pair',0,1))
        self.assertEqual(cert['topk']['active_boundary'],('pair',1,2))
        self.assertTrue(c.strict_guard(cert['topk']['radius_squared'],Q(1,4)))
        self.assertFalse(c.strict_guard(cert['topk']['radius_squared'],Q(1,3)))
        self.assertTrue(c.strict_guard(cert['top1']['radius_squared'],Q(1,3)))
        self.assertFalse(c.strict_guard(cert['top1']['radius_squared'],Q(1,2)))
        for typ in ('top1','topk'):
            shift=c.sharp_boundary_displacement(rows,cert['exact_preactivations'],cert[typ])
            self.assertEqual(c.squared_norm(shift),cert[typ]['radius_squared'])

    def test_normalization_physical_hidden_metric(self):
        # Standardization rescales the physical Jacobian in exactly one dim.
        W=((2,0),(-2,0),(0,0))
        rows,offs=c.affine_normalized_encoder(W,(1,0,-1),(5,7),(2,4))
        self.assertEqual(rows,((Q(1),Q(0)),(Q(-1),Q(0)),(Q(0),Q(0))))
        self.assertEqual(offs,(Q(-4),Q(5),Q(-1)))
        a=c.scores_at(rows,offs,(Q(6),Q(7)))
        self.assertEqual(a,(Q(2),Q(-1),Q(-1)))
        self.assertEqual(c.distance_squared(2,rows[0]),Q(4))
        self.assertIsNone(c.distance_squared(2,rows[2]))

    def test_selection_topk_vs_top1_can_cross_in_either_order(self):
        # The top two neuron order can change without changing top2 support.
        rows=((Q(1),),(Q(-1),),(Q(0),))
        offs=(Q(2),Q(2),Q(-10))
        cert=c.topk_selection_certificate(rows,offs,(Q(1,10),),k=2)
        self.assertGreater(cert['topk']['radius_squared'],cert['top1']['radius_squared'])
        self.assertGreater(cert['topk']['dyadic_sqrt_lower'],cert['top1']['dyadic_sqrt_lower'])
        # A weak selected kth neuron can instead cross an unselected third
        # long before the top1 identity is threatened.
        rows2=((Q(1),),(Q(-1),),(Q(2),))
        offs2=(Q(2),Q(1),Q(0))
        cert2=c.topk_selection_certificate(rows2,offs2,(Q(0),),k=2)
        self.assertLess(cert2['topk']['radius_squared'],cert2['top1']['radius_squared'])

    def test_dyadic_sqrt_exact_enclosures_and_strict_boundary(self):
        for q in (Q(1,9),Q(2),Q(0),Q(4),Q(7,11),Q(1,10**12)):
            low,hi=c.dyadic_sqrt_bracket(q,bits=40)
            self.assertLessEqual(low*low,q)
            self.assertGreaterEqual(hi*hi,q)
            self.assertLessEqual(hi-low,Q(1,2**40))
            self.assertEqual(c.strict_guard(q,low),low*low<q)
        for bad in (-1, Q(-1,10)):
            with self.assertRaises(ValueError):c.dyadic_sqrt_bracket(bad)

    def test_abstain_on_zero_or_tied_support(self):
        rows=((Q(1),),(Q(0),),(Q(-1),))
        with self.assertRaises(ValueError):
            c.topk_selection_certificate(rows,(Q(0),Q(0),Q(0)),(Q(0),),k=2)
        with self.assertRaises(ValueError):
            c.topk_selection_certificate(rows,(Q(0),Q(1),Q(0)),(Q(0),),k=2)
        with self.assertRaises(ValueError):
            c.affine_normalized_encoder(((1,2),), (0,), (0,0), (1,0))
        with self.assertRaises(ValueError):
            c.exact_cell((1,1),((1,),(0,)),(0,))
        with self.assertRaises(ValueError):
            c.strict_guard(Q(1),-1)

    def test_synthetic_finite_boundary_witness(self):
        rows=((Q(2,3),Q(1,4)),(Q(1,3),Q(-1,3)),(Q(-1,5),Q(2,7)))
        offsets=(Q(3),Q(2),Q(0))
        h=(Q(1,2),Q(-1,7))
        cert=c.topk_selection_certificate(rows,offsets,h,k=2)
        for key in ('top1','topk'):
            d=c.sharp_boundary_displacement(rows,cert['exact_preactivations'],cert[key])
            new=tuple(hj+dj for hj,dj in zip(h,d))
            vals=c.scores_at(rows,offsets,new)
            mode,i,j=cert[key]['active_boundary']
            if mode=='zero':
                self.assertEqual(vals[i],0)
            else:
                self.assertEqual(vals[i],vals[j])
            self.assertEqual(c.squared_norm(d),cert[key]['radius_squared'])


if __name__=='__main__':
    unittest.main()

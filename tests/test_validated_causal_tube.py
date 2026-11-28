"""OLM-08 finite exact-real norm and directional Taylor certificates."""
from fractions import Fraction as Q
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"research"/"orbit_lock"))
import validated_causal_tube as v


class CausalTubeTests(unittest.TestCase):
    def test_exact_dyadic_sqrt_frobenius_ceilings(self):
        for num,den in ((0,1),(1,4),(2,1),(9,4),(10007,999)):
            x=Q(num,den)
            hi=v.sqrt_upper(x,32)
            self.assertGreaterEqual(hi*hi,x)
            self.assertLess((hi-Q(1,1<<32))**2,x) if hi>0 and hi*hi!=x else None
        mat=((Q(3,5),Q(4,5)),(Q(0),Q(0)))
        upper=v.frobenius_upper(mat,32)
        self.assertGreaterEqual(upper,Q(1))

    def test_exact_composition_chain(self):
        c=v.composition_bounds(((2,3),(4,5)),7)
        self.assertEqual(c['jacobian'],Q(56))
        self.assertEqual(c['hessian'],Q(224))
        self.assertEqual(c['trace'][0],(Q(2),Q(3)))
        self.assertEqual(c['trace'][1],(Q(8),Q(32)))

    def test_layernorm_and_smooth_mlp_global_bounds(self):
        ln=v.layernorm_bounds([1]*48,Q(1,100),48,32)
        self.assertGreaterEqual(ln[0],10)
        self.assertGreaterEqual(ln[1],Q(50,3))
        a,b=v.linear_mlp_bounds(((1,0),(0,1)),((1,0),(0,1)))
        self.assertGreaterEqual(a,Q(9,4))
        self.assertGreaterEqual(b,Q(4,5))

    def test_finite_radius_tangent_separation_and_null(self):
        low,high=v.directional_interval(0,Q(1,4),1)
        self.assertEqual((low,high),(Q(0),Q(1,32)))
        self.assertTrue(v.dominance_certificate(3,1,Q(1,10),2))
        self.assertFalse(v.dominance_certificate(3,1,2,2))
        self.assertLessEqual(Q(1,32),high)
        self.assertEqual(v.directional_interval(1,Q(1,10),0),(Q(1,10),Q(1,10)))

    def test_locked_architecture_tensor_and_weight_guards(self):
        n=48
        mat=((1,0),(0,1))
        vals={
            'block.tok_mix.0.weight':mat,
            'block.tok_mix.2.weight':mat,
            'block.chan_mix.0.weight':mat,
            'block.chan_mix.2.weight':mat,
            'block.ln1.weight':[1]*n,
            'block.ln2.weight':[1]*n,
            'head.weight':mat,
        }
        s=v.source_model_global_certificate(vals,24)
        self.assertEqual(s['num_elementary_stages'],12)
        self.assertGreater(s['global_jacobian_upper'],0)
        self.assertGreater(s['global_hessian_upper'],0)
        del vals['head.weight']
        with self.assertRaises(ValueError):v.source_model_global_certificate(vals)

    def test_invalid_parameters(self):
        with self.assertRaises(ValueError):v.sqrt_upper(-1)
        with self.assertRaises(ValueError):v.frobenius_upper([])
        with self.assertRaises(ValueError):v.layernorm_bounds([1],0)
        with self.assertRaises(ValueError):v.composition_bounds(((1,-1),),1)
        with self.assertRaises(ValueError):v.directional_interval(1,-1,2)


if __name__=="__main__":
    unittest.main()

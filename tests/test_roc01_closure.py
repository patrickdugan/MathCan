"""ROC-01 closure-sweep geometry on a fully known synthetic 8D system.

No neural checkpoint is claimed or inferred. The public source declares
T and G exactly, and all 128 rank-matched conditional random completions
are generated from the registered base seeds.
"""
import math
import unittest

try:
    import numpy as np
except ImportError:
    np=None

from research.observer_calculus.closure_sweep import sweep, RANK_GRID, NULL_SEEDS


@unittest.skipIf(np is None, "NumPy required for source-level closure sweep")
class TestSyntheticClosureSweep(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        T=np.eye(8)
        T[0,2]=1.
        cls.T=T
        G=np.zeros((2,8))
        G[0,0]=1.
        G[1,1]=1.
        cls.G=G

    def test_svd_bounds_and_rank_grid(self):
        receipt=sweep(self.T,self.G,state_id="synth_8_source_0",
                      checkpoint_sha256="source_only_no_nn_checkpoint",
                      output_name="two_immediate_linear_outputs",horizon=4)
        self.assertEqual(tuple(receipt["rank_grid"]),RANK_GRID)
        self.assertEqual(receipt["readout_rank"],2)
        self.assertEqual(receipt["horizon"],4)
        self.assertEqual(receipt["source_claim"],"measured T and G required; no refitting")
        rows={r["k"]:r for r in receipt["rows"] if r["status"] == "sampled_upper_and_certified_theoretical_lower"}
        self.assertEqual(set(rows),{2,3,4,7,8})
        self.assertEqual({r["k"]:r["status"] for r in receipt["rows"]}[1],
                         "rank_below_declared_readout")
        self.assertEqual(rows[2]["observability_rank_at_N"],3)
        self.assertGreater(rows[2]["L_lower_svd"],0.)
        for k in (2,3,4,7,8):
            r=rows[k]
            self.assertLessEqual(r["L_lower_svd"],r["L_upper_sampled"]+1e-9)
            self.assertFalse(r["sweep_is_global_optimum"])
            self.assertEqual(r["random_count"],128)
            if r["conditional_null_degenerate"]:
                self.assertIsNone(r["one_sided_rank_p_for_svd_candidate"])
            else:
                self.assertGreaterEqual(r["one_sided_rank_p_for_svd_candidate"],1/129)
                self.assertLessEqual(r["one_sided_rank_p_for_svd_candidate"],1)
        self.assertAlmostEqual(rows[8]["L_upper_sampled"],0.,places=10)
        self.assertLess(rows[4]["L_upper_sampled"],1e-8)

    def test_registered_null_key_determinism(self):
        a=sweep(self.T,self.G,state_id="synth_8_source_0",
                checkpoint_sha256="source_only_no_nn_checkpoint",
                output_name="two_immediate_linear_outputs",horizon=4)
        b=sweep(self.T,self.G,state_id="synth_8_source_0",
                checkpoint_sha256="source_only_no_nn_checkpoint",
                output_name="two_immediate_linear_outputs",horizon=4)
        self.assertEqual(a,b)
        self.assertEqual(len(NULL_SEEDS),128)
        c=sweep(self.T,self.G,state_id="synth_8_source_1",
                checkpoint_sha256="source_only_no_nn_checkpoint",
                output_name="two_immediate_linear_outputs",horizon=4)
        # k=2 equals rank(G), so there is no free random subspace and its
        # exact B is source-key independent. At k=4 the random extension is
        # genuinely randomized and the seeded medians must differ.
        aa={r["k"]:r for r in a["rows"]}
        cc={r["k"]:r for r in c["rows"]}
        self.assertTrue(aa[2]["conditional_null_degenerate"])
        self.assertIsNone(aa[2]["one_sided_rank_p_for_svd_candidate"])
        self.assertFalse(aa[4]["conditional_null_degenerate"])
        self.assertNotEqual(aa[4]["random_median"],cc[4]["random_median"])

    def test_invalid_g_and_horizon(self):
        with self.assertRaises(ValueError):
            sweep(self.T,[[1.,2.]],state_id="s",checkpoint_sha256="c",
                  output_name="g",horizon=4)
        with self.assertRaises(ValueError):
            sweep(self.T,self.G,state_id="s",checkpoint_sha256="c",
                  output_name="g",horizon=9)


if __name__=="__main__":
    unittest.main()

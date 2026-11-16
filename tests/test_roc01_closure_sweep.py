"""ROC-01 optional NumPy sampled-bound calculation, no neural checkpoint."""
import unittest
from research.observer_calculus.closure_sweep import sweep


class ClosureSweepTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            import numpy
        except ImportError:
            raise unittest.SkipTest("NumPy required for exact checkpoint rank sweep")

    def test_three_dim_rotation_exact_k_two_cost(self):
        T=[[1,0,0],[0,0,-1],[0,1,0]]
        G=[[1,0,0]]
        d=sweep(T,G,state_id="rotation_toy",checkpoint_sha256="synthetic",
                output_name="first",horizon=3)
        r=next(row for row in d["rows"] if row["k"]==2)
        self.assertEqual(r["k"],2)
        self.assertEqual(r["status"],"sampled_upper_and_certified_theoretical_lower")
        self.assertEqual(r["observability_rank_at_N"],1)
        self.assertAlmostEqual(r["L_lower_svd"],0.,places=12)
        self.assertAlmostEqual(r["L_upper_sampled"],1.,places=10)
        self.assertEqual(r["random_count"],128)
        self.assertFalse(r["sweep_is_global_optimum"])
        self.assertEqual(r["lower_bound_norm"],"operator_2")

    def test_five_dimensional_interior_parity_k2_k3_k4(self):
        T=[[1,0,0,0,0],[0,0,-1,0,0],[0,1,0,0,0],
           [0,0,0,0,-1],[0,0,0,1,0]]
        r=sweep(T,[[1,0,0,0,0]],state_id="parity5",
                checkpoint_sha256="synthetic",output_name="first",horizon=5)
        by_k={row["k"]:row for row in r["rows"]}
        for k in (2,4):
            self.assertAlmostEqual(by_k[k]["L_upper_sampled"],1,places=8)
        self.assertAlmostEqual(by_k[3]["L_upper_sampled"],0,places=8)
        self.assertIn(7,r["rank_grid"])

    def test_full_rank_identity(self):
        T=[[1 if i==j else 0 for j in range(4)] for i in range(4)]
        G=[[1,0,0,0]]
        d=sweep(T,G,state_id="identity",checkpoint_sha256="synthetic",
                output_name="first",horizon=4)
        for r in d["rows"]:
            if r["k"]<=4:
                self.assertAlmostEqual(r["L_upper_sampled"],0.,places=10)

    def test_observer_rank_below_readout_is_inadmissible(self):
        T=[[1 if i==j else 0 for j in range(12)] for i in range(12)]
        G=[[int(i==j) for j in range(12)] for i in range(11)]
        d=sweep(T,G,state_id="head11",checkpoint_sha256="synthetic",
                output_name="head_logits",horizon=2)
        self.assertEqual({r["k"]:r["status"] for r in d["rows"]}[8],
                         "rank_below_declared_readout")
        self.assertEqual({r["k"]:r["status"] for r in d["rows"]}[16],
                         "rank_exceeds_dimension")

if __name__=="__main__":
    unittest.main()

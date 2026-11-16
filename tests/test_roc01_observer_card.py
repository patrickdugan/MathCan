"""ROC-01 algebraic and reproducibility checks; no checkpoint model data."""
import math
import unittest
from research.observer_calculus.observer_card import (
    score_state, null_distribution, rank_p, holm, norm_match, random_basis,
    complement, causal_gram, calibrate_state,
)

class TestObserverCard(unittest.TestCase):
    def test_register_and_driver(self):
        T=[[1.,2.,0.],[0.,1.,0.],[0.,0.,1.]]
        U=[[1.],[0.],[0.]]
        r=score_state(T,U,[[[1.,0.,0.]]])
        self.assertAlmostEqual(r["B_normalized"],1.)
        self.assertEqual(r["A_frob"],0.)
        self.assertEqual(r["C_frob"],0.)
        self.assertIn("output_register",r["legacy_absolute_threshold_tags"])
        self.assertEqual(r["tags"],["unclassified"])
        self.assertIn("invariant_subspace",r["legacy_absolute_threshold_tags"])
        self.assertAlmostEqual(r["s_causal"],1.)

    def test_latched_memory_and_irrelevant_have_equal_dynamics(self):
        T=[[1.,0.,0.],[2.,1.,0.],[0.,0.,1.]]
        U=[[1.],[0.],[0.]]
        latched=score_state(T,U,[[[1.,0.,0.]]])
        irrelevant=score_state(T,U,[[[0.,1.,0.]]])
        self.assertEqual(latched["A_frob"],irrelevant["A_frob"])
        self.assertEqual(latched["B_frob"],irrelevant["B_frob"])
        self.assertIn("latched_memory",latched["legacy_absolute_threshold_tags"])
        self.assertIn("irrelevant",irrelevant["legacy_absolute_threshold_tags"])
        self.assertEqual(latched["C_normalized"],1.)

    def test_gauge_change_sign_and_complement(self):
        T=[[1.,0.,0.],[2.,1.,0.],[0.,3.,1.]]
        u=[[1.],[0.],[0.]]
        plus=score_state(T,u,[[[0.,1.,0.]]])
        minus=score_state(T,[[-1.],[0.],[0.]],[[[0.,1.,0.]]])
        for field in ("A_frob","B_frob","C_frob","s_causal"):
            self.assertAlmostEqual(plus[field],minus[field],places=12)
        q=complement(u)
        self.assertEqual(len(q),3)
        self.assertEqual(len(q[0]),2)

    def test_128_seed_rank_matched_null(self):
        T=[[1.,2.,0.],[0.,1.,0.],[0.,0.,1.]]
        U=[[1.],[0.],[0.]]; J=[[1.,0.,0.]]
        n=null_distribution(T,U,[J],state_key="state01",checkpoint_sha="toy")
        self.assertEqual(n["n"],128)
        self.assertEqual(n,null_distribution(T,U,[J],state_key="state01",checkpoint_sha="toy"))
        actual=score_state(T,U,[J])
        p=rank_p(actual["B_normalized"],[r["B_normalized"] for r in n["rows"]],smaller=False)
        self.assertGreaterEqual(p,1/129)
        self.assertLessEqual(p,1.)
        with self.assertRaises(ValueError):
            rank_p(1.,[0.]*8,smaller=True)

    def test_zero_dynamics_null_H(self):
        card=score_state([[1.,0.],[0.,1.]],[[1.],[0.]],[[[0.,0.]]])
        self.assertTrue(card["zero_dynamics"])
        self.assertIsNone(card["s_causal"])
        self.assertIsNone(card["task_mse"])

    def test_normalize_intervention_and_familywise_p(self):
        r=norm_match([3.,4.,0.],[0.,0.,1.])
        self.assertAlmostEqual(math.dist(r,[0.,0.,0.]),5.)
        self.assertEqual(holm([0.01,0.04,0.03,0.30]),[0.04,0.09,0.09,0.30])

    def test_calibrated_register_and_null_penalty(self):
        T=[[1.,2.,0.],[0.,1.,0.],[0.,0.,1.]]
        U=[[1.],[0.],[0.]]; J=[[1.,0.,0.]]
        c=score_state(T,U,[J])
        null=null_distribution(T,U,[J],state_key="registered",checkpoint_sha="toy")
        self.assertEqual(null["distinct_subspaces"],128)
        r=calibrate_state(c,null)
        self.assertEqual(r["tag_status"],"null_calibrated")
        self.assertIn("output_register",r["tags"])
        self.assertGreater(r["b_penalty_ratio_squared"],1)
        self.assertLessEqual(r["holm_adjusted_p"]["b_large"],0.05)
        altered=dict(null)
        altered["rows"]=[dict(x) for x in null["rows"]]
        altered["rows"][1]["basis_subspace_sha256"]=altered["rows"][0]["basis_subspace_sha256"]
        self.assertEqual(calibrate_state(c,altered)["tag_status"],
                         "insufficient_distinct_rank_null")

    def test_isotropic_D_abstains_when_B_null_degenerate(self):
        d=8; T=[[2. if i==j else 0. for j in range(d)] for i in range(d)]
        U=[[float(j==i) for j in range(2)] for i in range(d)]
        J=[[1.]+[0.]*(d-1)]
        c=score_state(T,U,[J])
        null=null_distribution(T,U,[J],state_key="isotropic",checkpoint_sha="toy")
        r=calibrate_state(c,null)
        self.assertEqual(r["tags"],["unclassified"])
        self.assertIsNone(r["b_penalty_ratio_squared"])

    def test_invalid_inputs_rejected(self):
        with self.assertRaises(ValueError):
            score_state([[1.,0.],[0.,1.]],[[1.],[1.]],[[[1.,0.]]])
        with self.assertRaises(ValueError):
            score_state([[1.,0.],[0.,1.]],[[1.],[0.]],[[[1.,0.]]],task_mse=-1.)
        with self.assertRaises(ValueError):
            norm_match([1.],[0.])
        with self.assertRaises(ValueError):
            causal_gram([[[1.,0.]]],[0.])

if __name__=="__main__":
    unittest.main()

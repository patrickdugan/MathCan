"""ROC-01 exact rational counterexamples BEFORE proof claims, d<=6."""
from fractions import Fraction as F
from itertools import product
import random
import unittest

from research.observer_calculus import theory as t


class ExactTheoryTests(unittest.TestCase):
    def test_finite_separation_has_rank_one_witness(self):
        self.assertTrue(t.rank_one_four_codes()["distinct"])

    def test_rotation_has_nonmonotone_exact_rank_closure(self):
        c=t.no_rank2_extension_rotation()
        self.assertEqual(c["closure_rank"],1)
        self.assertTrue(c["all_B2_eq_one"])
        self.assertEqual([r["B2"] for r in c["rank2_witnesses"]],[F(1)]*4)

    def test_five_dimensional_parity_witness_is_interior(self):
        r=t.rotation5_interior_parity()
        self.assertTrue(r["interior_nonmonotone"])
        self.assertEqual(r["B2_for_canonical_witnesses"],
                         {2:F(1),3:F(0),4:F(1)})

    def test_minimal_observability_span_full_rank(self):
        T=t.rat([[0,1,0],[0,0,1],[0,0,0]])
        G=t.rat([[1,0,0]])
        self.assertEqual(t.closure_rank(T,G),3)
        self.assertEqual(t.rank(t.observable(T,G,2)),2)

    def test_bound_540_exact_rational_instances_d_le_six(self):
        rng=random.Random(20261116)
        checks=0
        for d in range(2,7):
            for _ in range(12):
                T=t.rat([[rng.randint(-2,2) for j in range(d)] for i in range(d)])
                G=t.rat([[1]+[0]*(d-1)])
                for k in range(1,d):
                    U=t.rat([[int(i==j) for j in range(k)] for i in range(d)])
                    Q=t.rat([[int(i==j+k) for j in range(d-k)] for i in range(d)])
                    for N in (2,3,4):
                        r=t.exact_energy_bound(T,G,U,Q,N)
                        self.assertTrue(r["holds"])
                        checks+=1
        self.assertEqual(checks,540)

    def test_observer_must_contain_readout_for_bound(self):
        T=t.eye(2);G=t.rat([[0,1]])
        U=t.rat([[1],[0]]);Q=t.rat([[0],[1]])
        with self.assertRaises(ValueError):
            t.exact_energy_bound(T,G,U,Q,2)

    def test_bpd_minimum_cover_three_types_of_intervention(self):
        arms=t.min_separating_arm_set(t.IDEAL_SIGNATURES)
        self.assertEqual(arms,("dark_to_observed","observed_to_dark","observed_to_observed"))
        self.assertEqual(len(t.all_min_separating_arm_sets(t.IDEAL_SIGNATURES)),3)
        self.assertIsNone(t.min_separating_arm_set(t.CORRECTED_FREEZE_SIGNATURES))
        self.assertEqual(t.CORRECTED_FREEZE_SIGNATURES["invariant_subspace"],
                         t.CORRECTED_FREEZE_SIGNATURES["output_register"])

    def test_synthetic_chernoff_allocation_is_probability_simplex(self):
        means={s:{k:F(v) for k,v in m.items()} for s,m in t.IDEAL_SIGNATURES.items()}
        variances={k:F(1) for k in next(iter(means.values()))}
        a=t.chernoff_grid(means,variances)
        self.assertEqual(sum(a["allocation"]),1)
        self.assertGreater(a["worst_pair_KL"],0)
        self.assertEqual(a["step"],F(1,20))
        with self.assertRaises(ValueError):
            t.gaussian_pair_kl(0,1,0)


    def test_exact_ideal_chernoff_optimum_uses_readout_control(self):
        """A 3-arm separating cover may need 4 arms at optimal KL allocation."""
        from research.observer_calculus.theory import ideal_four_arm_chernoff_exact
        r=ideal_four_arm_chernoff_exact()
        self.assertEqual(r["minimum_separating_arm_count"],3)
        self.assertTrue(r["allocation_uses_all_four_arms"])
        self.assertEqual(r["worst_pair_KL"],F(1,5))
        self.assertEqual(r["analytic_upper_bound_KL"],F(1,5))
        self.assertEqual(r["allocation"]["ablate_readout"],F(1,5))
        self.assertEqual(r["allocation"]["observed_to_observed"],F(2,5))

if __name__=="__main__":
    unittest.main()

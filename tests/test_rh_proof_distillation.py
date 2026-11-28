"""Exact source-inspired RH scalar checks; no mathematical black-box assumptions."""
import unittest
from dataclasses import replace

from research.rh_proof_distillation.rh_window_feasibility import (
    CLAUSES, WindowParams, campaign as window_campaign, dyadic_witness,
    evaluate, evaluate_scale, scale_witness,
)
from research.rh_proof_distillation.rh_joint_scalar_envelope import (
    campaign as joint_campaign, bounds, enlarged_scale,
)


class RHSourceWindowTests(unittest.TestCase):
    def test_sixteen_pinned_scalar_windows(self):
        receipt = window_campaign()
        self.assertEqual(len(CLAUSES), 16)
        self.assertEqual(len(receipt["positive_examples"]), 5)
        self.assertTrue(all(p["passes"] == 16 and p["all_pass"] for p in receipt["positive_examples"]))

    def test_sizewindows_negative_controls(self):
        valid = dyadic_witness(1)
        near = evaluate(replace(valid, n=valid.n - 1))
        self.assertFalse(near["checks"]["k_cap"])
        self.assertFalse(near["all_pass"])
        self.assertFalse(window_campaign()["negative_controls"][1]["checks"]["eventual_x"])

    def test_stronger_original_source_regime(self):
        for level in (6, 7):
            result = evaluate_scale(scale_witness(level))
            self.assertEqual((result["passes"], result["total"]), (12, 12))
            self.assertEqual(result["sizewindows_passes"], 16)
            self.assertTrue(result["all_scale_checks_pass"])
            self.assertTrue(result["sizewindows_pass"])
        self.assertFalse(evaluate_scale(dyadic_witness(6))["checks"]["SizesAt_n_lower"])

    def test_large_x_sufficient_and_cost_window(self):
        receipt = joint_campaign()
        self.assertEqual(len(receipt["cases"]), 2)
        self.assertFalse(receipt["negative_control"]["short_scale_passes_sufficient_8x5_exp_test"])
        for example in receipt["cases"]:
            self.assertTrue(example["all_sufficient_gates_pass"])
            self.assertTrue(example["all_scale_and_sizewindow"])
            self.assertFalse(example["full_scale_structure_proved"])
            self.assertFalse(example["full_analytic_or_geometric_witness_proved"])

    def test_large_x_independent_case(self):
        a = bounds(enlarged_scale(6))
        self.assertEqual(a["x_log2"], 16384)
        self.assertEqual(a["sizewindows_scalar_passes"], 16)
        self.assertEqual(a["source_scale_passes"], 12)

    def test_bounded_exact_power_guard(self):
        from fractions import Fraction
        p = dyadic_witness(1)
        self.assertEqual(p.power(Fraction(3, 16)), 64)
        with self.assertRaises(ValueError):
            p.power(Fraction(1, 7))


if __name__ == "__main__":
    unittest.main()

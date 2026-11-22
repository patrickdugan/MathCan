"""Parser tests independent of Lean, mathlib, and a network connection."""

import unittest
from research.bsar_audit.source_gate import TARGETS, assess_source, theorem_signature


class TestBSARStatementAudit(unittest.TestCase):
    def test_extract_multiline_signature_without_proof_body(self):
        src = """-- irrelevant comment

theorem step7_leray_quadratic_doubling_closure
    {M d0 dfinal : Int} {K : Nat}
    (h_M_pos : 0 < M)
    (hchain : LerayDoublingChain M K d0 dfinal) :
    dfinal ≤ Pow2 K * d0 := by
  induction hchain with
  | refl d => omega
"""
        sig = theorem_signature(src, "step7_leray_quadratic_doubling_closure")
        self.assertIn("hchain : LerayDoublingChain", sig)
        self.assertIn("{K : Nat}", sig)
        self.assertNotIn("induction", sig)

    def test_detects_missing_theorems(self):
        report = assess_source("theorem unrelated (x : Int) : x = x := by rfl")
        self.assertFalse(report["all_found"])
        self.assertEqual(len(report["theorems"]), len(TARGETS))
        self.assertTrue(all(not item["found"] for item in report["theorems"]))

    def test_classification_requires_actual_analytic_objects(self):
        src = """theorem step7_holder_half_cone_biot_savart_bound
    (x1 y1 R K_xi d1 : Int)
    (h_holder_cone : x1 ≤ K_xi * d1) :
    x1 ≤ K_xi * d1 := by
  exact h_holder_cone
"""
        item = next(r for r in assess_source(src)["theorems"] if r["found"])
        self.assertEqual(item["premise_names"], ["h_holder_cone"])
        self.assertTrue(item["uses_integer_parameters"])
        self.assertFalse(item["declares_real_or_pde_objects"])

    def test_ignores_commentary_as_a_theorem(self):
        self.assertIsNone(theorem_signature("-- theorem step7_leray_quadratic_doubling_closure",
                                            "step7_leray_quadratic_doubling_closure"))


if __name__ == "__main__":
    unittest.main()

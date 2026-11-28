"""Offline invariants for the BSA-R theorem-boundary RLT dataset."""

import json
import unittest

from research.bsar_audit.boundary_curriculum import (
    CATALOG, check_dataset, generate, round_split
)


class TestBSARBoundaryCurriculum(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.catalog = json.loads(CATALOG.read_text(encoding="utf-8"))
        cls.rows = generate(cls.catalog)

    def test_catalog_has_all_six_rounds(self):
        self.assertEqual(self.catalog["total"], 129)
        self.assertEqual(len(self.catalog["rounds"]), 6)
        self.assertEqual(sum(group["count"] for group in self.catalog["rounds"]), 129)

    def test_no_real_analytic_declarations_at_snapshot(self):
        declarations = [decl for group in self.catalog["rounds"] for decl in group["declarations"]]
        self.assertTrue(all(not d["has_real_analytic"] for d in declarations))
        self.assertTrue(any(d["has_abstract_R"] for d in declarations))

    def test_no_cross_split_name_leakage(self):
        metrics = check_dataset(self.rows)
        self.assertGreater(metrics["unique_roots"], 60)
        self.assertGreater(metrics["examples"], 300)
        self.assertEqual(set(metrics["split_counts"]), {"train", "dev", "test"})
        self.assertEqual(round_split("lean/Step7VorticityDirectionPdeRound6.lean"), "test")
        self.assertEqual(round_split("lean/Step6BiotSavartCommutatorRound5.lean"), "dev")

    def test_seed_reproducibility(self):
        self.assertEqual(self.rows, generate(self.catalog))
        self.assertEqual(set(row["id"] for row in self.rows),
                         set(row["id"] for row in generate(self.catalog, seed=10)))

    def test_claims_keep_source_evidence(self):
        for example in self.rows:
            self.assertEqual(example["evidence_type"], "STATIC_LEAN_SOURCE_ONLY")
            self.assertIn(example["source_path"], example["prompt"])
            self.assertIn("Lean signature:", example["prompt"])
            self.assertIn("gold_reason", example)
        labels = {row["gold_label"] for row in self.rows}
        self.assertIn("KERNEL_CHECK_REQUIRED", labels)
        self.assertIn("UNSUPPORTED_PDE_LIFT", labels)


if __name__ == "__main__":
    unittest.main()

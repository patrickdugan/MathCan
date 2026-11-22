"""Check archived theorem signatures extracted from the pinned BSA-R source."""

import json
import unittest
from pathlib import Path


class TestBSARPinnedSnapshot(unittest.TestCase):
    def test_snapshot_names_and_domains(self):
        path = Path(__file__).resolve().parents[1] / "research/bsar_audit/pinned_declarations.json"
        snapshot = json.loads(path.read_text(encoding="utf-8"))
        self.assertEqual(snapshot["commit"], "80c62433b0eb671175bd8d6169822d3ebd922b60")
        self.assertEqual(len(snapshot["signatures"]), 5)
        self.assertTrue(all(item["has_int_parameters"] for item in snapshot["signatures"]))
        self.assertFalse(any(item["has_smooth_pde_types"] for item in snapshot["signatures"]))

    def test_doubling_chain_is_explicit_premise(self):
        path = Path(__file__).resolve().parents[1] / "research/bsar_audit/pinned_declarations.json"
        snapshot = json.loads(path.read_text(encoding="utf-8"))
        doubling = next(s for s in snapshot["signatures"] if s["name"] == "step7_leray_quadratic_doubling_closure")
        self.assertIn("hchain", doubling["premises"])
        self.assertIn("LerayDoublingChain M K d0 dfinal", doubling["signature"])


if __name__ == "__main__":
    unittest.main()

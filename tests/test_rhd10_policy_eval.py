"""RHD-10B blinded evaluator and finite-policy reproducibility tests."""
from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from research.rh_proof_distillation.rhd10_rank_one_repair import (
    episodes, verify,
)
from research.rh_proof_distillation.rhd10_policy_eval import (
    FrequencyPolicy, build_report, candidate_from_snapshot, public_episode,
    redact_failure, write_report,
)


class RHD10PolicyEvalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = list(episodes())
        cls.report = build_report(cls.rows)

    def test_teacher_fields_and_expected_targets_are_masked(self):
        row = next(r for r in self.rows if r["split"] == "test")
        exposed = public_episode(row)
        self.assertEqual(
            set(exposed),
            {"root_id", "selected_factor", "source_prime",
             "candidate", "local_probe"},
        )
        self.assertFalse(any("oracle" in key for key in exposed))
        self.assertNotIn("true_norm", exposed["local_probe"])
        self.assertNotIn("q_norm", exposed["local_probe"])
        self.assertNotIn("verifier_feedback", exposed)
        observations = [
            redact_failure(f) for f in verify(candidate_from_snapshot(exposed["candidate"]))
        ]
        self.assertTrue(observations)
        for observation in observations:
            self.assertNotIn("expected", observation)
            self.assertNotIn("oracle_actions", observation)
        with self.assertRaises(ValueError):
            FrequencyPolicy.fit([row])

    def test_trained_table_covers_known_fault_grammar(self):
        learned = FrequencyPolicy.fit(
            [r for r in self.rows if r["split"] == "train"]
        )
        keys = set(learned.table)
        self.assertEqual(len(keys), 11)
        self.assertEqual(
            set(self.report["learned_action_keys"]), keys,
        )
        self.assertIn("global_norm_pullback", keys)
        self.assertIn("exact_conductor", keys)
        self.assertIn("idele_unit_normalization", keys)
        self.assertIn("local_character:0", keys)
        self.assertIn("missing_exception:3", keys)
        self.assertEqual(learned.choose({"gate": "verified"}), {"kind": "STOP"})

    def test_full_feedback_open_loop_is_necessary_control(self):
        self.assertEqual(sum(self.report["split_counts"].values()), 3364)
        for phase in ("val", "test"):
            learned = self.report["results"][phase]["trained_frequency"]
            ceiling = self.report["results"][phase]["privileged_rule_ceiling"]
            n = learned["sparse_recurrent"]["episodes"]
            self.assertEqual(learned["sparse_recurrent"]["solved"], n)
            self.assertEqual(learned["full_open_loop"]["solved"], n)
            self.assertEqual(learned["full_open_loop"]["total_verifier_calls"], 2 * n)
            self.assertLess(learned["sparse_one_step"]["solved"], n)
            self.assertEqual(learned["sparse_recurrent"]["invalid_edits"], 0)
            self.assertEqual(learned["full_open_loop"]["invalid_edits"], 0)
            self.assertGreater(
                learned["full_open_loop"]["verified_repairs_per_100_verifier_calls"],
                learned["sparse_recurrent"]["verified_repairs_per_100_verifier_calls"],
            )
            self.assertEqual(
                learned["sparse_recurrent"]["solved"],
                ceiling["sparse_recurrent"]["solved"],
            )
            self.assertEqual(learned["sparse_recurrent"]["stop_accuracy"], 1.0)

    def test_changes_to_heldout_teacher_labels_cannot_change_scores(self):
        modified = deepcopy(self.rows)
        for row in modified:
            if row["split"] != "train":
                row["oracle_actions"] = [{"kind": "MALICIOUS_LABEL"}]
                row["oracle_steps"] = -99
                row["oracle_terminal"] = {"poison": True}
                row["one_step_budget_pass"] = False
                row["verifier_feedback"] = [{"expected": "poison"}]
        self.assertEqual(self.report, build_report(modified))

    def test_byte_identical_report_and_sha256_receipt(self):
        with tempfile.TemporaryDirectory() as tmp:
            destination = Path(tmp) / "policy_eval.json"
            first = write_report(destination)
            serialized = destination.read_bytes()
            digest = destination.with_suffix(".sha256").read_text()
            self.assertEqual(digest.split()[0], hashlib.sha256(serialized).hexdigest())
            self.assertEqual(first, json.loads(serialized))
            self.assertEqual(first, write_report(destination))
            self.assertEqual(serialized, destination.read_bytes())
            self.assertFalse(first["proof_term_data"])


if __name__ == "__main__":
    unittest.main()

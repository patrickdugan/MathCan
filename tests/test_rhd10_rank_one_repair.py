"""Independent RHD-10 mutation, split, stopping and determinism checks."""
import tempfile
import unittest
from pathlib import Path

from research.rh_proof_distillation.rhd09_local_character import (
    P, P2, dirichlet_exponent, principal_norm, theta,
)
from research.rh_proof_distillation.rhd10_rank_one_repair import (
    ALL_PLACES, FACTORS, TRUE_COEFFS, apply_action, clean_candidate,
    create_episode, episodes, fault_catalog, inject_fault, snapshot,
    split_for_root, suggested_action, verify, write_data,
)


class RankOneRepairTests(unittest.TestCase):
    def test_local_character_global_norm_witnesses(self):
        self.assertEqual(len(FACTORS), 4)
        self.assertEqual(tuple(f[1] % P for f in FACTORS), TRUE_COEFFS)
        for f in FACTORS:
            self.assertEqual(theta(f, 15, 0), 1)
            self.assertEqual(principal_norm(f, 15, 0), 30)
            self.assertEqual(dirichlet_exponent(principal_norm(f, 15, 0)), 1)
            self.assertEqual(dirichlet_exponent(1), 0)
            self.assertEqual(dirichlet_exponent(-1), 0)
        self.assertEqual(dirichlet_exponent(1 + P), 1)

    def test_clean_all_four_selected_places(self):
        for w0 in ALL_PLACES:
            s = clean_candidate(w0)
            self.assertEqual(s.exceptions, ALL_PLACES - {w0})
            self.assertEqual(len(s.exceptions), 3)
            self.assertEqual(verify(s), [])

    def test_independent_mutation_gates_and_repairs(self):
        for w0 in ALL_PLACES:
            clean = clean_candidate(w0)
            self.assertEqual(len(fault_catalog(w0)), 10)
            for fault in fault_catalog(w0):
                s = inject_fault(clean, fault, shift=3)
                bad = verify(s)
                self.assertEqual(len(bad), 1, (w0, fault, bad))
                fixed = apply_action(s, suggested_action(bad[0]))
                self.assertEqual(fixed, clean, (w0, fault))
                self.assertEqual(verify(fixed), [])
                self.assertNotEqual(snapshot(s), snapshot(clean))

    def test_multiple_errors_and_recurrent_stopping(self):
        for w0 in ALL_PLACES:
            s = clean_candidate(w0)
            for fault in (f"local:{w0}", "global_sign", "conductor"):
                s = inject_fault(s, fault, shift=2)
            self.assertEqual(len(verify(s)), 3)
            for remaining in (2, 1, 0):
                s = apply_action(s, suggested_action(verify(s)[0]))
                self.assertEqual(len(verify(s)), remaining)
            self.assertEqual(verify(s), [])

    def test_train_validation_test_roots_are_input_disjoint(self):
        groups = {"train": set(), "val": set(), "test": set()}
        for w0 in range(4):
            for a in range(P):
                for b in range(P):
                    root = (w0, a, b)
                    groups[split_for_root(*root)].add(root)
        self.assertEqual(sum(map(len, groups.values())), 4 * P * P)
        self.assertFalse(groups["train"] & groups["val"])
        self.assertFalse(groups["train"] & groups["test"])
        self.assertFalse(groups["val"] & groups["test"])
        self.assertTrue(all(groups.values()))

    def test_oracle_episodes_valid_for_every_root(self):
        counts = {1: 0, 2: 0, 3: 0}
        roots = set()
        for episode in episodes():
            self.assertNotIn(episode["root_id"], roots)
            roots.add(episode["root_id"])
            k = episode["oracle_steps"]
            self.assertIn(k, (1, 2, 3))
            counts[k] += 1
            self.assertEqual(len(episode["verifier_feedback"]), k)
            self.assertTrue(episode["oracle_actions"][-1]["verifier_pass"])
            self.assertEqual(episode["oracle_actions"][-1]["kind"], "STOP")
            self.assertEqual(episode["oracle_actions"][-2]["remaining_violations"], 0)
            self.assertFalse(episode["lean_witness_proved"])
            self.assertFalse(episode["automorphic_witness_proved"])
        self.assertEqual(len(roots), 4 * P * P)
        self.assertTrue(all(counts.values()))

    def test_corpus_manifest_byte_replay(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / "rank_one_repair.jsonl"
            first = write_data(target)
            second = write_data(target)
            self.assertEqual(first, second)
            self.assertEqual(first["examples"], 3364)
            self.assertEqual(sum(first["counts"].values()), 3364)
            self.assertEqual(first["oracle_budget_success"]["three_step"], 3364)
            self.assertLess(first["oracle_budget_success"]["one_step"], 3364)
            self.assertLess(first["oracle_budget_success"]["two_step"], 3364)
            self.assertFalse(first["proof_term_data"])


if __name__ == "__main__":
    unittest.main()

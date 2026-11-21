"""Offline mutation tests for source-derived RH family quantifier ledger."""
import unittest

from research.rh_proof_distillation.family_quantifier_source_audit import (
    DEFINITIONS, GATES, FAMILY_BRIDGE, declaration_slice, git_blob,
    inspect_text,
)


class FamilyQuantifierSourceTests(unittest.TestCase):
    def test_git_blob_identity(self):
        self.assertEqual(git_blob(b""), "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391")

    def test_exact_boundary_fails_on_missing_declaration(self):
        with self.assertRaises(ValueError):
            declaration_slice("theorem different := by", "def AllLargeC ")

    def test_varying_witness_would_fail_uniform_gate_check(self):
        fragments = GATES["AllLargeC"][1]
        src = ("def AllLargeC " + " ∧ ".join(
            s.replace("∀ x : ℝ, x0 ≤ x → ∀ i : (Fm ε h0 h1).Ix x,",
                      "∀ x : ℝ, x0 ≤ x → ∃ i : (Fm ε h0 h1).Ix x,")
            for s in fragments
        ) + "\n")
        _, body = declaration_slice(src, "def AllLargeC ")
        self.assertNotIn(fragments[-1], body)

    def test_bridge_requirements_are_source_attestable(self):
        self.assertIn("TOPF", GATES)
        self.assertIn("SizesFe", GATES)
        self.assertIn("proposition_eleven_two_at_scale", FAMILY_BRIDGE[1])


if __name__ == "__main__":
    unittest.main()

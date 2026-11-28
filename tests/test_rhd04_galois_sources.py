"""RHD-04 source-statement equivalence and mutation controls."""
import unittest
from research.rh_proof_distillation.galois_row_input_audit import (
    git_blob, definition_body, normalize_lift_statement, compare_lifts, F, REQUIRED,
)


class GaloisRowInputTests(unittest.TestCase):
    def test_source_pin_manifest_is_complete(self):
        self.assertEqual(len(F), 12)
        self.assertTrue(all(len(entry[1]) == 40 for entry in F.values()))
        self.assertEqual(set(F), set(REQUIRED))

    def test_definition_extraction(self):
        source = "def TLiftK : Prop := A\n\ndef Other : Prop := True\n"
        self.assertEqual(definition_body(source, "def TLiftK : Prop :="), "A")
        with self.assertRaises(ValueError):
            definition_body(source, "def DoesNotExist : Prop :=")
        self.assertEqual(definition_body("def TLiftK : Prop := True\nend", "def TLiftK : Prop :="), "True")

    def test_namespace_and_whitespace_normalization(self):
        a = " W.GoodK \n  ∃ d₀ : ℕ, ∀ d, d₀ ≤ d   W.IsSkew IsHecke HasExp ∃ U' : Submodule"
        b = a.replace("W.GoodK", "_root_.UpperTheory.TP.W.GoodK")
        self.assertEqual(normalize_lift_statement(a), normalize_lift_statement(b))
        a = "def TLiftK : Prop := " + a + "\nend"
        b = "def TLift_k : Prop := " + b + "\ndef HgtFst_k : Prop := True"
        self.assertTrue(compare_lifts(a, b)["same_after_namespace_and_whitespace_normalization"])
        with self.assertRaisesRegex(ValueError, "not the same"):
            compare_lifts(a, b.replace("W.IsSkew", "W.IsHerm"))

    def test_git_empty_blob(self):
        self.assertEqual(git_blob(b""), "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391")


if __name__ == "__main__":
    unittest.main()

"""RHD-05 source contract mutation and field-count checks."""
import unittest

from research.rh_proof_distillation.galois_row_deep_audit import (
    EXPECTED_FIELDS, REQUIRED, SOURCES, blob_sha, proof_fields, verify_source,
)


class DeepGaloisTests(unittest.TestCase):
    def test_manifest_complete(self):
        self.assertEqual(len(SOURCES), 11)
        self.assertEqual(set(SOURCES), set(REQUIRED))
        self.assertTrue(all(len(x[1]) == 40 for x in SOURCES.values()))

    def test_exact_field_names(self):
        self.assertEqual(len(EXPECTED_FIELDS["steps"]), 17)
        self.assertEqual(len(EXPECTED_FIELDS["ks_plan"]), 6)
        for label, structure in (("steps", "Steps"), ("ks_plan", "KSAll")):
            body = "structure " + structure + " : Prop where\n"
            body += "".join("  " + f + " : Prop\n" for f in EXPECTED_FIELDS[label])
            body += "\ntheorem next : True := trivial\n"
            self.assertEqual(proof_fields(body, structure), EXPECTED_FIELDS[label])
            with self.assertRaisesRegex(ValueError, "fields changed"):
                # Replacing one proof field must invalidate the contract.
                original = "\n  " + EXPECTED_FIELDS[label][0] + " :"
                mutated = body.replace(original, "\n  bogus :")
                anchors = (s for s in REQUIRED[label] if not s.startswith("structure "))
                full = "\n".join(anchors) + "\n" + mutated
                verify_source(label, full)

    def test_missing_supplier_and_mutation_gate(self):
        for label in SOURCES:
            text = "\n".join(REQUIRED[label])
            if label not in EXPECTED_FIELDS:
                self.assertEqual(verify_source(label, text)["matched_anchors"], len(REQUIRED[label]))
                with self.assertRaisesRegex(ValueError, "lost pinned"):
                    verify_source(label, text.replace(REQUIRED[label][0], "mutated"))
        self.assertEqual(blob_sha(b""), "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391")


if __name__ == "__main__":
    unittest.main()

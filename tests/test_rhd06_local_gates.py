"""RHD-06 source mutation controls and residue compatibility certificate."""
import unittest

from research.rh_proof_distillation.geo_theta_local_gates_audit import (
    REQUIRED, SOURCES, blob, quadratic_agreement, residue_model, source_contract,
)


class RHD06LocalGateTests(unittest.TestCase):
    def test_source_manifest(self):
        self.assertEqual(len(SOURCES), 6)
        self.assertEqual(set(SOURCES), set(REQUIRED))
        self.assertTrue(all(len(item[1]) == 40 for item in SOURCES.values()))

    def test_exact_oneK_sameK_statement(self):
        suffix = "∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {x} → (y ∈ w.asIdeal ↔ y ∈ w'.asIdeal)"
        def header(name):
            return f"def {name} (x : E) (w w' : HeightOneSpectrum (𝓞 E)) : Prop :=\n  "
        self.assertEqual(
            quadratic_agreement(header("OneK") + suffix, "OneK"),
            quadratic_agreement(header("SameK") + suffix, "SameK"),
        )
        self.assertNotEqual(
            quadratic_agreement(header("SameK") + suffix.replace("↔", "→"), "SameK"),
            quadratic_agreement(header("OneK") + suffix, "OneK"),
        )

    def test_source_anchor_mutations(self):
        for label, anchors in REQUIRED.items():
            source = "\n".join(anchors)
            self.assertEqual(source_contract(label, source), len(anchors))
            with self.assertRaisesRegex(ValueError, "missing source anchors"):
                source_contract(label, source.replace(anchors[0], "mutation"))
        damaged = "\n".join(REQUIRED["theta"]).replace("∃ U' : Submodule", "fake marker")
        with self.assertRaises(ValueError):
            source_contract("theta", damaged)

    def test_mod_29_prime_reductions(self):
        r = residue_model()
        self.assertEqual(r["imaginary_roots"], [12, 17])
        self.assertEqual(r["real_roots"], [11, 18])
        self.assertEqual(r["pair"], [[12, 11], [12, 18]])
        with self.assertRaises(ValueError):
            residue_model(11)

    def test_git_empty_blob(self):
        self.assertEqual(blob(b""), "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391")


if __name__ == "__main__":
    unittest.main()

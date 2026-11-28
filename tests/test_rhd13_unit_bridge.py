"""RHD-13 independent finite character annihilator parity tests."""
import tempfile
import unittest
from pathlib import Path

from research.rh_proof_distillation.rhd13_unit_bridge import (
    EXPECTED, certify_pair, determinant, normalized, report, write_report,
)
from research.rh_proof_distillation.rhd10_unit_obstruction import (
    obstruction_receipt as zeta20_receipt,
)
from research.rh_proof_distillation.rhd11_crossfamily import (
    unit_obstruction as zeta24_receipt,
)


class UnitBridgeTests(unittest.TestCase):
    def test_all_eight_frozen_vectors_and_determinants(self):
        output = report()
        self.assertEqual(output["kernel_expected_theorems"], 8)
        self.assertEqual(output["nonzero_linear_functionals_surviving"], 0)
        self.assertEqual(len(output["finite_fields"]), 2)
        for source in output["finite_fields"]:
            e = EXPECTED[source["source_family"]]
            self.assertEqual(source["p"],e["p"])
            self.assertEqual(len(source["places"]),4)
            for j,row in enumerate(source["places"]):
                self.assertEqual(tuple(map(tuple,row["vectors"])), e["vectors"][j])
                self.assertEqual(row["determinant_mod_p"],e["determinants"][j])
                self.assertEqual(row["nonzero_functionals_killing_both_units"],0)

    def test_pair_mutation_controls_reject_singular_spans(self):
        for _, e in EXPECTED.items():
            p=e["p"]
            for vectors in e["vectors"]:
                v,w=vectors
                self.assertEqual(certify_pair(v,w,p),determinant(v,w,p))
                with self.assertRaises(ValueError):
                    certify_pair(v,v,p)
                with self.assertRaises(ValueError):
                    certify_pair((0,0),w,p)

    def test_normalized_reports_replay_original_sources(self):
        p29=normalized("zeta20_p29",zeta20_receipt())
        p5=normalized("zeta24_p5",zeta24_receipt())
        self.assertEqual(p29["unit_norm_products_mod_p2"],[1,1])
        self.assertEqual(p5["unit_norm_products_mod_p2"],[1,1])
        self.assertEqual(p29["dirichlet_exponent_sums_mod_p"],[0,0])
        self.assertEqual(p5["dirichlet_exponent_sums_mod_p"],[0,0])
        self.assertEqual(tuple(r["determinant_mod_p"] for r in p29["places"]),
                         (16,26,26,16))
        self.assertEqual(tuple(r["determinant_mod_p"] for r in p5["places"]),
                         (2,4,1,3))

    def test_determinism_and_evidence_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            target=Path(directory)/"rhd13_unit_bridge.json"
            first=write_report(target)
            blob=target.read_bytes()
            second=write_report(target)
            self.assertEqual(first,second)
            self.assertEqual(blob,target.read_bytes())
            self.assertTrue(target.with_suffix(".sha256").exists())
            self.assertFalse(first["p_adic_global_witness_proved"])
            self.assertFalse(first["automorphic_witness_proved"])


if __name__=="__main__":
    unittest.main()

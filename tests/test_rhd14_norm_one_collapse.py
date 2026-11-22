"""RHD-14 independent local conjugation and norm-one collapse tests."""
import tempfile
import unittest
from pathlib import Path

from research.rh_proof_distillation.rhd14_norm_one_collapse import (
    FAMILIES, all_witnesses, check_ring_conjugation,
    conjugate_coordinates, conjugate_factor_indices, first_layer_witness,
    norm_in_quotient, receipt, write_data,
)


class NormOneCollapseTests(unittest.TestCase):
    def test_conjugate_pair_involution_and_lifted_opposition(self):
        for fam in FAMILIES:
            indices = conjugate_factor_indices(fam)
            self.assertEqual(indices, (3, 2, 1, 0) if fam.p == 29 else
                             (2, 3, 0, 1))
            for j in range(4):
                k = indices[j]
                self.assertNotEqual(j, k)
                self.assertEqual(indices[k], j)
                d, c, _ = fam.factors[j]
                d2, c2, _ = fam.factors[k]
                self.assertEqual(d*d2 % (fam.p**2), 1)
                self.assertEqual(c2*d % (fam.p**2), c % (fam.p**2))

    def test_full_first_layer_norm_and_character_equivariance(self):
        expected = sum(4*fam.p*fam.p for fam in FAMILIES)
        self.assertEqual(expected,3464)
        records = list(all_witnesses())
        self.assertEqual(len(records), expected)
        for fam in FAMILIES:
            for j in range(4):
                for a in range(fam.p):
                    for b in range(fam.p):
                        record=first_layer_witness(fam,j,a,b)
                        self.assertEqual(record["norm_one_ratio_exponent"],0)
                        self.assertEqual(
                            record["local_norm_character"],
                            fam.trace(fam.factors[j],a,b),
                        )
        self.assertEqual(
            sum(1 for row in records if row["norm_one_ratio_exponent"]),
            0,
        )

    def test_general_quadratic_norm_conjugation(self):
        for fam in FAMILIES:
            m=fam.p**2
            idx=conjugate_factor_indices(fam)
            # Exhaustive small field; reproducible modular samples in 29-adic field.
            basis=range(m) if fam.p==5 else range(0,m,13)
            for j in range(4):
                k=idx[j]
                for a in basis:
                    for b in basis:
                        a2,b2=conjugate_coordinates(fam,j,a,b)
                        self.assertEqual(
                            norm_in_quotient(fam.factors[j],a,b,m),
                            norm_in_quotient(fam.factors[k],a2,b2,m),
                        )
            result=check_ring_conjugation(fam,samples=64)
            self.assertEqual(result["checked_pairs"],256)

    def test_nontrivial_characters_cancel_on_paired_places(self):
        for fam in FAMILIES:
            half=(fam.p+1)//2
            for j in range(4):
                r=first_layer_witness(fam,j,half,0)
                self.assertEqual(r["local_norm_character"],1)
                self.assertEqual(r["conjugate_norm_character"],1)
                self.assertEqual(r["norm_one_ratio_exponent"],0)

    def test_finite_negative_control_asymmetric_local_candidate(self):
        # An asymmetric local character would produce a nonzero ratio,
        # but this does not certify its existence as a global Hecke character.
        for fam in FAMILIES:
            for j in range(4):
                e=first_layer_witness(fam,j,(fam.p+1)//2,0)
                self.assertNotEqual(
                    (e["local_norm_character"]-0) % fam.p,0,
                )

    def test_manifest_replay_and_evidence_boundary(self):
        with tempfile.TemporaryDirectory() as tmp:
            f=Path(tmp)/"norm_collapse.json"
            a=write_data(f)
            data=f.read_bytes()
            rows=f.with_suffix(".jsonl").read_bytes()
            self.assertEqual(a,write_data(f))
            self.assertEqual(data,f.read_bytes())
            self.assertEqual(rows,f.with_suffix(".jsonl").read_bytes())
            self.assertEqual(a["first_layer_cases"],3464)
            self.assertTrue(a["all_norm_one_ratio_exponents_zero"])
            self.assertFalse(a["original_TyEll_proved"])
            self.assertFalse(a["original_UA_identified_in_kernel"])
            self.assertTrue(f.with_suffix(".sha256").exists())


if __name__=="__main__":
    unittest.main()

"""RHD-15 finite split-torus character, repair and leakage-gate tests."""
import tempfile
import unittest
from pathlib import Path

from research.rh_proof_distillation.rhd15_split_torus_character import (
    FAMILIES, all_faults, apply_action, check_nontrivial_character,
    clean_candidate, episodes, generate, inject_fault, orbit, pair_witness,
    real_orbits, root_of_unity_controls, same_real_place, suggested_action,
    quadratic_subfield_tag, oneK_apart_candidate, residue_pow,
    verify, write_data,
)


class SplitTorusCharacterTests(unittest.TestCase):
    def test_two_real_place_orbits_and_conjugate_pairs(self):
        expected = {
            29: ((0, 3), (1, 2)),
            5: ((0, 2), (1, 3)),
        }
        for fam in FAMILIES:
            self.assertEqual(real_orbits(fam), expected[fam.p])
            for j in range(4):
                selected = orbit(fam, j)
                self.assertEqual(len(selected), 2)
                mate = next(k for k in selected if k != j)
                self.assertTrue(same_real_place(fam, j, mate))
                for k in range(4):
                    self.assertEqual(same_real_place(fam,j,k), k in selected)

    def test_transverse_quadratic_and_real_subfield_contractions(self):
        tags = {29: (17,12,17,12), 5: (2,3,3,2)}
        partner = {29: (2,3,0,1), 5: (3,2,1,0)}
        for fam in FAMILIES:
            values = tuple(quadratic_subfield_tag(fam,j) for j in range(4))
            self.assertEqual(values,tags[fam.p])
            for j in range(4):
                k = oneK_apart_candidate(fam,j)
                self.assertEqual(k,partner[fam.p][j])
                self.assertNotEqual(j,k)
                self.assertEqual(quadratic_subfield_tag(fam,j),
                                 quadratic_subfield_tag(fam,k))
                self.assertFalse(same_real_place(fam,j,k))
                exponent = 5 if fam.p==29 else 6
                power = residue_pow(fam.factors[j], exponent, fam.p)
                self.assertEqual(power,(values[j],0))

    def test_exhaustive_norm_one_pair_and_nontriviality(self):
        cases = 0
        nonzero = 0
        for fam in FAMILIES:
            check_nontrivial_character(fam)
            for j in range(4):
                for a in range(fam.p):
                    for b in range(fam.p):
                        row = pair_witness(fam,j,a,b)
                        self.assertEqual(row["absolute_norm_pullback_exponent"], 0)
                        self.assertEqual(
                            (row["selected_character"]+row["partner_character"])%fam.p,
                            0)
                        self.assertTrue(row["same_real_place"])
                        nonzero += int(row["selected_character"] != 0)
                        cases += 1
        self.assertEqual(cases, 3464)
        self.assertEqual(nonzero, 4*(29*29-29)+4*(5*5-5))

    def test_cyclotomic_roots_and_local_character_compatibility(self):
        for fam in FAMILIES:
            receipt = root_of_unity_controls(fam)
            self.assertEqual(len(receipt["checks"]), 4)
            for item in receipt["checks"]:
                self.assertEqual(item["order"], 20 if fam.p == 29 else 24)
                self.assertTrue(item["all_root_of_unity_character_exponents_zero"])

    def test_each_fault_isolated_and_repairable(self):
        self.assertEqual(len(all_faults()), 5)
        for fam in FAMILIES:
            for j in range(4):
                gold = clean_candidate(fam,j)
                self.assertEqual(verify(fam,j,gold), [])
                for fault in all_faults():
                    broken=inject_fault(fam,j,gold,fault)
                    failures=verify(fam,j,broken)
                    self.assertEqual(len(failures),1,(fam.label,j,fault,failures))
                    repaired=apply_action(broken,suggested_action(fam,j,failures[0]))
                    self.assertEqual(repaired,gold)
                    self.assertEqual(verify(fam,j,repaired),[])

    def test_all_root_trajectories_and_clean_stop(self):
        rows = list(episodes())
        self.assertEqual(len(rows),3464)
        self.assertEqual(len({r["root_id"] for r in rows}),3464)
        self.assertTrue(any(r["oracle_steps"]==0 for r in rows))
        self.assertTrue(any(r["oracle_steps"]==3 for r in rows))
        counts = {"train":0,"val":0,"test":0,"crossfamily_test":0}
        for r in rows:
            counts[r["split"]]+=1
            self.assertEqual(len(r["verifier_gates"]),r["oracle_steps"])
            self.assertEqual(len(r["oracle_actions"]),r["oracle_steps"]+1)
            self.assertEqual(r["oracle_actions"][-1]["action"]["kind"],"STOP")
            self.assertTrue(r["oracle_actions"][-1]["verifier_pass"])
            self.assertFalse(r["automorphic_character_proved"])
            self.assertEqual(r["oracle_terminal"]["exceptional_factors"], [])
        self.assertEqual(counts["crossfamily_test"], 100)
        self.assertEqual(sum(counts.values()),3464)
        self.assertTrue(all(counts.values()))

    def test_split_is_family_disjoint_and_deterministic(self):
        a = list(episodes())
        b = list(episodes())
        self.assertEqual(a,b)
        self.assertEqual(
            {r["p"] for r in a if r["split"]=="crossfamily_test"}, {5})
        self.assertEqual(
            {r["p"] for r in a if r["split"]!="crossfamily_test"}, {29})

    def test_manifest_replay_and_evidence_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            target=Path(directory)/"rhd15.jsonl"
            receipt=write_data(target)
            blob=target.read_bytes()
            self.assertEqual(receipt,write_data(target))
            self.assertEqual(blob,target.read_bytes())
            self.assertEqual(receipt["episodes"],3464)
            self.assertEqual(receipt["crossfamily_training_examples"],0)
            self.assertIsNone(receipt["trained_model_scores"])
            self.assertFalse(receipt["original_TyEll_proved"])
            self.assertFalse(receipt["global_Hecke_character_proved"])
            self.assertTrue(target.with_suffix(".manifest.json").exists())


if __name__=="__main__":
    unittest.main()

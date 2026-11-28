"""RHD-16 independent cyclic character lift and repair verification."""
import tempfile
import unittest
from pathlib import Path

from research.rh_proof_distillation.rhd16_cyclic_extension import (
    PRIMES, TORSION_ORDERS, FAULTS,
    action_for, apply_action, clean, episodes, exact_extension_certificate,
    inject, local_exponent, split_for, valid_generator_exponents,
    verify, write_data,
)


class CyclicCharacterExtensionTests(unittest.TestCase):
    def test_every_local_exponent_has_exactly_p_global_lifts(self):
        for p in PRIMES:
            for target in range(p):
                lifts = valid_generator_exponents(p, target)
                self.assertEqual(len(lifts), p)
                self.assertEqual(lifts, [target+p*k for k in range(p)])
                self.assertTrue(all(local_exponent(p,e,p*p)==target for e in lifts))
                self.assertTrue(all((p*e)%(p*p)==p*target for e in lifts))

    def test_mu_p_extension_necessarily_trivial_on_pG(self):
        for p in PRIMES:
            for exponent in range(p):
                self.assertEqual(local_exponent(p,exponent,p),0)
                for target in range(1,p):
                    self.assertNotEqual(local_exponent(p,exponent,p),target)
            receipt=exact_extension_certificate(p)
            self.assertEqual(receipt["valid_mu_p_extensions_for_local_exponent_1"],0)
            self.assertEqual(receipt["valid_mu_p2_extensions_for_local_exponent_1"],p)
            self.assertTrue(receipt["all_nontrivial_local_targets_need_mu_p2"])

    def test_global_root_of_unity_twists_rejected(self):
        for p in PRIMES:
            n=TORSION_ORDERS[p]
            self.assertEqual(set(k for k in range(p) if (n*k)%p==0),{0})
            self.assertTrue(exact_extension_certificate(p)[
                "cyclotomic_root_twists_forced_zero"
            ])

    def test_all_isolated_mutations_repair_to_clean(self):
        for p in PRIMES:
            for target in (1,p-1):
                good=clean(p,target)
                self.assertEqual(verify(good),[])
                for fault in FAULTS:
                    bad=inject(good,fault)
                    feedback=verify(bad)
                    self.assertEqual(len(feedback),1,(p,target,fault))
                    fixed=apply_action(bad,action_for(bad,feedback[0]))
                    self.assertEqual(fixed,good)
                    self.assertEqual(verify(fixed),[])

    def test_all_recurrent_roots_and_explicit_stopping(self):
        rows=list(episodes())
        self.assertEqual(len(rows),sum(p*p for p in PRIMES))
        self.assertEqual(len({r["root_id"] for r in rows}),len(rows))
        self.assertTrue(all(n in {r["oracle_steps"] for r in rows} for n in range(4)))
        self.assertEqual(sum(r["split"]=="cross_prime_test" for r in rows),25)
        self.assertEqual({r["prime"] for r in rows if r["split"]=="cross_prime_test"},{5})
        self.assertEqual({r["prime"] for r in rows if r["split"]!="cross_prime_test"},{29})
        for row in rows:
            k=row["oracle_steps"]
            self.assertEqual(len(row["verifier_failures"]),k)
            self.assertEqual(len(row["oracle_actions"]),k+1)
            self.assertEqual(row["oracle_actions"][-1]["action"]["kind"],"STOP")
            self.assertEqual(row["oracle_terminal"]["output_order"],row["prime"]**2)
            self.assertFalse(row["actual_adelic_character_proved"])
            self.assertFalse(row["original_TyEll_proved"])

    def test_deterministic_dataset_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            target=Path(directory)/"cyclic_extension.jsonl"
            result=write_data(target)
            data=target.read_bytes()
            self.assertEqual(result,write_data(target))
            self.assertEqual(data,target.read_bytes())
            self.assertEqual(result["episodes"],866)
            self.assertEqual(result["splits"]["cross_prime_test"],25)
            self.assertEqual(sum(result["splits"].values()),866)
            self.assertIsNone(result["trained_neural_scores"])
            self.assertFalse(result["global_character_proved"])
            self.assertFalse(result["original_TyEll_proved"])
            self.assertTrue(target.with_suffix(".manifest.json").exists())


if __name__=="__main__":
    unittest.main()

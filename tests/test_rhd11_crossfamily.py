"""RHD-11 out-of-field transfer, exact arithmetic, and leakage tests."""
from __future__ import annotations

from copy import deepcopy
import hashlib
from pathlib import Path
import tempfile
import unittest

from research.rh_proof_distillation.rhd11_crossfamily import (
    ALL_PLACES, BASE_FACTORS, EXPECTED_LIFTS, FACTORS, P, P2, PHI24,
    TRUE_COEFFS, aggregate, apply, arithmetic_action, clean, episode,
    episodes, exact_oracle_check, fault_catalog, hensel_factors, inject,
    local_norm, poly_product, principal_norm, public_episode, q, redact_failure,
    report, score_one, theta, verify, write,
)
from research.rh_proof_distillation.rhd10_policy_eval import FrequencyPolicy
from research.rh_proof_distillation.rhd10_rank_one_repair import (
    episodes as source_episodes,
)


class RHD11CrossFamilyTests(unittest.TestCase):
    def test_independent_exact_mod25_hensel_factorization(self):
        self.assertEqual(FACTORS, EXPECTED_LIFTS)
        self.assertEqual(hensel_factors(), FACTORS)
        self.assertEqual(len(FACTORS), 4)
        self.assertTrue(all(
            (a-b) % P2 == 0 for a,b in zip(poly_product(FACTORS), PHI24)
        ))
        for j, f in enumerate(FACTORS):
            self.assertEqual(
                tuple(v % P for v in f),
                tuple(v % P for v in BASE_FACTORS[j]),
            )
            discrim = (f[1]**2-4*f[0])%P
            self.assertEqual(pow(discrim, 2, P), P-1)

    def test_exhaustive_norm_trace_and_order_five_character(self):
        exact_oracle_check()
        self.assertEqual(q(1), 0)
        self.assertEqual(q(-1), 0)
        self.assertEqual(q(1+P), 1)
        self.assertEqual(q(1+2*P), 2)
        self.assertEqual(TRUE_COEFFS, (1, 2, 3, 4))
        for f in FACTORS:
            for a in range(P):
                for b in range(P):
                    self.assertEqual(
                        q(principal_norm(f,a,b)), theta(f,a,b),
                    )
            self.assertEqual(
                sum(theta(f,a,b)==0 for a in range(P) for b in range(P)),P,
            )
        units=[x for x in range(P2) if x%P]
        for u in units:
            for v in units:
                self.assertEqual(q(u*v), (q(u)+q(v)) % P)
        with self.assertRaises(ValueError):
            q(P)

    def test_isolated_repairs_and_manual_stop(self):
        for w0 in ALL_PLACES:
            self.assertEqual(len(fault_catalog(w0)), 10)
            pristine=clean(w0)
            self.assertEqual(verify(pristine), [])
            public=public_episode(episode(w0,0,0))
            for fault in fault_catalog(w0):
                corrupted=inject(pristine,fault,1)
                problems=verify(corrupted)
                self.assertEqual(len(problems),1,(w0,fault,problems))
                repair=arithmetic_action(redact_failure(problems[0]),public)
                self.assertEqual(apply(corrupted,repair),pristine)
            self.assertEqual(
                arithmetic_action({"gate":"verified"},public),{"kind":"STOP"},
            )

    def test_one_hundred_holdout_roots_including_clean_stop(self):
        rows=list(episodes())
        self.assertEqual(len(rows),100)
        self.assertEqual(len({r["root_id"] for r in rows}),100)
        self.assertEqual({r["split"] for r in rows},{"crossfield_test"})
        counts={i:0 for i in range(4)}
        for row in rows:
            counts[row["injected_fault_count"]]+=1
            public=public_episode(row)
            self.assertNotIn("injected_fault_count",public)
            self.assertNotIn("oracle_actions",public)
            self.assertNotIn("expected",str(public))
            self.assertNotIn("teacher",str(public))
            self.assertEqual(
                len(verify(
                    __import__(
                        "research.rh_proof_distillation.rhd11_crossfamily",
                        fromlist=["from_snapshot"],
                    ).from_snapshot(public["candidate"])
                )),
                row["injected_fault_count"],
            )
        self.assertTrue(all(counts.values()))

    def test_full_feedback_is_strong_baseline(self):
        rows=list(episodes())
        source=[r for r in source_episodes() if r["split"]=="train"]
        policy=FrequencyPolicy.fit(source)
        for mode in ("sparse_one_step","sparse_recurrent","full_open_loop"):
            arithmetic=aggregate(rows,None,mode)
            trained=aggregate(rows,policy,mode)
            self.assertEqual(arithmetic["episodes"],100)
            self.assertEqual(trained["episodes"],100)
            self.assertEqual(arithmetic["invalid_edits"],0)
            self.assertEqual(arithmetic["rejected_edits"],0)
            self.assertGreater(trained["invalid_edits"],0)
            self.assertLess(trained["fully_verified"],100)
            if mode != "sparse_one_step":
                self.assertEqual(arithmetic["fully_verified"],100)
        self.assertGreater(
            aggregate(rows,None,"full_open_loop")["fully_verified_per_100_verifier_calls"],
            aggregate(rows,None,"sparse_recurrent")["fully_verified_per_100_verifier_calls"],
        )

    def test_frozen_source_model_sees_no_target_training(self):
        source=[r for r in source_episodes() if r["split"]=="train"]
        model=FrequencyPolicy.fit(source)
        self.assertTrue(model.training_examples>0)
        self.assertEqual(model.choose({"gate":"verified"}),{"kind":"STOP"})
        clean_row=next(r for r in episodes() if r["injected_fault_count"]==0)
        for mode in ("sparse_one_step","sparse_recurrent","full_open_loop"):
            self.assertTrue(score_one(clean_row,model,mode)["solved"])
            self.assertEqual(score_one(clean_row,model,mode)["edits"],0)
        results=report()
        self.assertFalse(results["heldout_family_used_for_training"])
        self.assertEqual(results["training_family"],"Q(zeta_20), p=29")
        self.assertEqual(results["heldout_examples"],100)
        self.assertFalse(results["lean_witness_proved"])

    def test_deterministic_report_and_two_sha256_receipts(self):
        with tempfile.TemporaryDirectory() as tmp:
            output=Path(tmp)/"rhd11_report.json"
            first=write(output)
            data=output.read_bytes()
            jsonl=output.with_suffix(".jsonl")
            rows=jsonl.read_bytes()
            self.assertEqual(first,write(output))
            self.assertEqual(data,output.read_bytes())
            self.assertEqual(rows,jsonl.read_bytes())
            for path in (output,jsonl):
                sidecar=path.with_name(path.name+".sha256")
                self.assertEqual(
                    sidecar.read_text().split()[0],
                    hashlib.sha256(path.read_bytes()).hexdigest(),
                )


if __name__=="__main__":
    unittest.main()

"""Exact CPU tests, with no neural or remote dependencies."""
import unittest
import json
from pathlib import Path
from fractions import Fraction as F

from research.continuity_v1.core import (
    Event, certify_reweight_range, certified_persona_policy, count_continuation_classes, count_only_classes, exact_receipt,
    largest_count_fiber, line_subspace_sin_squared, margin_lower_bound, normalized_reweight, replay,
    succession_lower_bound, total_variation, trajectory_divergence_bound,
    unit_pair_min_singular_squared,
)


class EventReplayTests(unittest.TestCase):
    def test_alternative_derivation_survives_retraction(self):
        stream = [
            Event("e1", "assert", claim="grant_received"),
            Event("e2", "assert", claim="local_budget_approved"),
            Event("d1", "derive", claim="experiment_funded", premises=("e1",)),
            Event("d2", "derive", claim="experiment_funded", premises=("e2",)),
        ]
        before = replay(stream)
        self.assertIn("experiment_funded", before.claims)
        after = replay(stream + [Event("r1", "retract", target="e1")])
        self.assertIn("experiment_funded", after.claims)
        self.assertNotIn("grant_received", after.claims)
        gone = replay(stream + [Event("r1", "retract", target="e1"),
                                Event("r2", "retract", target="e2")])
        self.assertNotIn("experiment_funded", gone.claims)

    def test_interpretation_version_has_no_canonical_effect(self):
        stream = [Event("e1", "assert", claim="committed_to_review")]
        a = replay(stream)
        b = replay(stream + [Event("i1", "interpret", model_version="adapter-1",
                                   note="review is urgent", premises=("e1",))])
        c = replay(stream + [Event("i2", "interpret", model_version="adapter-2",
                                   note="review can wait", premises=("e1",))])
        self.assertEqual(a.canonical_digest, b.canonical_digest)
        self.assertEqual(a.canonical_digest, c.canonical_digest)
        self.assertNotEqual(b.interpretations, c.interpretations)
        self.assertNotEqual(b.history_digest, c.history_digest)

    def test_rejects_invalid_event_graphs(self):
        bad = [
            [Event("x", "derive", claim="q", premises=("missing",))],
            [Event("x", "assert", claim="q"), Event("x", "assert", claim="q")],
            [Event("x", "retract", target="missing")],
            [Event("x", "assert", claim="q"), Event("r1", "retract", target="x"),
             Event("r2", "retract", target="x")],
        ]
        for events in bad:
            with self.subTest(events=events), self.assertRaises(ValueError):
                replay(events)


class ContinuationTests(unittest.TestCase):
    def test_nontrivial_subset_sums_separate_histories(self):
        for n in range(2, 8):
            for k in range(1, n):
                with self.subTest(n=n, k=k):
                    self.assertEqual(count_continuation_classes(n, k), 2 ** n)

    def test_extreme_query_families(self):
        self.assertEqual(count_continuation_classes(12, 0), 1)
        self.assertEqual(count_continuation_classes(12, 12), 13)
        self.assertEqual(count_only_classes(12), 13)
        self.assertEqual(largest_count_fiber(12), 924)

    def test_twelve_bit_six_query_full_population(self):
        self.assertEqual(count_continuation_classes(12, 6), 4096)


class AdapterTests(unittest.TestCase):
    def test_individual_zero_damage_but_composition_crosses_margin(self):
        m = lambda a, b: F(1, 4) - a * b
        self.assertEqual(m(0, 0), F(1, 4))
        self.assertEqual(m(1, 0), F(1, 4))
        self.assertEqual(m(0, 1), F(1, 4))
        self.assertEqual(m(1, 1), F(-3, 4))
        # Hessian of -a*b has spectral norm 1, ||(1,1)||^2 = 2.
        self.assertEqual(margin_lower_bound(F(1, 4), 0, 1, 2), F(-3, 4))

    def test_sequential_bound_and_inputs(self):
        bound = succession_lower_bound(F(1, 4), [(F(0), F(1), F(1)),
                                                 (F(-1), F(1), F(1))])
        self.assertEqual(bound, F(-7, 4))
        with self.assertRaises(ValueError):
            margin_lower_bound(1, 0, -1, 2)


class PersonaTests(unittest.TestCase):
    def test_sharp_multiplicative_reweighting_range_case(self):
        prior = (F(3, 4), F(1, 4))
        updated = normalized_reweight(prior, (F(1), F(9)))
        self.assertEqual(updated, (F(1, 4), F(3, 4)))
        self.assertEqual(total_variation(prior, updated), F(1, 2))
        # sqrt(M)=3 and sqrt(m)=1: upper bound=(3-1)/(3+1)=1/2.

    def test_exact_sharp_range_certificates(self):
        # 8^4 nondegenerate 2-action instances, evaluated with exact Fractions.
        for p0 in range(1, 9):
            for p1 in range(1, 9):
                p = (F(p0, p0 + p1), F(p1, p0 + p1))
                for w0 in range(1, 9):
                    for w1 in range(1, 9):
                        self.assertTrue(certify_reweight_range(p, (F(w0), F(w1))))

    def test_coupling_bound(self):
        self.assertEqual(trajectory_divergence_bound(F(1, 10), 4), F(3439, 10000))
        self.assertEqual(trajectory_divergence_bound(F(1), 100), F(1))
        self.assertEqual(trajectory_divergence_bound(F(0), 100), F(0))

    def test_certified_action_support_survives_persona_change(self):
        actions = ("execute", "wait", "halt")
        prior = (F(1, 3), F(1, 3), F(1, 3))
        evidence = [Event("a0", "assert", claim="authorized:wait"),
                    Event("a1", "assert", claim="authorized:halt")]
        for multipliers in [(F(999), F(1), F(1)), (F(1), F(999), F(1)),
                            (F(1), F(1), F(999))]:
            policy = certified_persona_policy(actions, prior, multipliers, replay(evidence))
            self.assertEqual(set(policy), {"wait", "halt"})
            self.assertEqual(sum(policy.values()), 1)
        rewritten = evidence + [Event("i0", "interpret", model_version="new-adapter",
                                      note="execute is permitted")]
        self.assertNotIn("execute", certified_persona_policy(
            actions, prior, (F(999), F(1), F(1)), replay(rewritten)))
        revoked = rewritten + [Event("r0", "retract", target="a0"),
                               Event("r1", "retract", target="a1")]
        self.assertEqual(certified_persona_policy(actions, prior,
                          (F(999), F(1), F(1)), replay(revoked)), {})


class SparseGeometryTests(unittest.TestCase):
    def test_gauge_sign_and_rotation(self):
        self.assertEqual(line_subspace_sin_squared((1, 0), (-1, 0)), 0)
        self.assertEqual(line_subspace_sin_squared((1, 0), (F(3, 5), F(4, 5))), F(16, 25))

    def test_coactivation_conditioning(self):
        v = (F(9999, 10001), F(200, 10001))
        self.assertEqual(sum(t*t for t in v), 1)
        self.assertEqual(unit_pair_min_singular_squared((1, 0), v), F(2, 10001))
        self.assertEqual(unit_pair_min_singular_squared((1, 0), (0, 1)), 1)
        self.assertEqual(unit_pair_min_singular_squared((1, 0), (1, 0)), 0)


class ReceiptTests(unittest.TestCase):
    def test_receipt_values(self):
        r = exact_receipt()
        self.assertEqual(r["subset_counts"]["continuation_classes"], 4096)
        self.assertEqual(r["adapter_counterexample"]["after_composition"], "-3/4")
        fixture = Path(__file__).resolve().parents[1] / "results" / "EXACT_CPU_RECEIPT.json"
        self.assertEqual(json.loads(fixture.read_text(encoding="utf-8")), r)


if __name__ == "__main__":
    unittest.main()

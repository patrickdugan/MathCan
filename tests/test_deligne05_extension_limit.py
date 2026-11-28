"""DEL-05 exact finite-shadow regressions for Hexagon Lemma 2."""
import unittest
from collections import Counter
from research.deligne_sign_audit.verify_del05_tasks import (
    CORPUS, inspect, verify_corpus,
)
import json

def data():
    return [json.loads(x) for x in CORPUS.read_text(encoding="utf-8").splitlines()
            if x.strip()]

class ExtensionBudgetTests(unittest.TestCase):
    def test_all_corpus_labels(self):
        counts=verify_corpus()
        self.assertEqual(sum(counts.values()),62)
        self.assertEqual(counts["valid"],30)

    def test_sublinear_family_finite_shadows(self):
        items=[x for x in data() if x["kind"]=="valid"]
        self.assertEqual(len(items),30)
        for x in items:
            with self.subTest(id=x["id"]):
                v=inspect(x)
                self.assertTrue(all(v["passes"]))
                self.assertTrue(v["target_present"])
                self.assertTrue(v["sublinear_family_witness"])
                self.assertLessEqual(x["c"]**2,x["k"])
                self.assertGreater(x["e"],0)

    def test_extension_degree_mutant(self):
        items=[x for x in data() if x["kind"]=="zero_extension"]
        self.assertEqual(len(items),6)
        for x in items:
            v=inspect(x)
            self.assertTrue(all(v["passes"]))
            self.assertFalse(v["e_positive"])
            self.assertFalse(v["conclusion"])

    def test_linear_exponent_loss_mutant(self):
        for x in (x for x in data() if x["kind"]=="linear_loss"):
            v=inspect(x)
            self.assertTrue(all(v["passes"]))
            self.assertEqual(x["c"],x["k"])
            self.assertFalse(v["conclusion"])

    def test_only_first_power_mutant(self):
        for x in (x for x in data() if x["kind"]=="one_power_only"):
            v=inspect(x)
            self.assertTrue(v["passes"][0])
            self.assertFalse(v["passes"][1])

    def test_virtual_trace_cancellation_mutant(self):
        for x in (x for x in data() if x["kind"]=="virtual_cancellation"):
            v=inspect(x)
            self.assertTrue(all(t==0 for t in v["traces"]))
            self.assertFalse(v["positive_multiplicities"])
            self.assertFalse(v["distinct"])

    def test_missing_tensor_eigenvalue_mutant(self):
        for x in (x for x in data() if x["kind"]=="missing_tensor_eigenvalue"):
            v=inspect(x)
            self.assertTrue(all(v["passes"]))
            self.assertFalse(v["target_present"])
            self.assertFalse(v["conclusion"])

if __name__=="__main__":
    unittest.main()

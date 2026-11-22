"""Exact rational BSAR-09 source-Ode versus weak-product controls."""

import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from bsar09_exact_oracle import (
    LABELS,
    REGIMES,
    SEED,
    check_corpus,
    export,
    frac,
    generate,
    oracle,
    public_rows,
    read_predictions,
    score,
)


class TestBSAR09FractionOracle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = generate()
        cls.report = check_corpus(cls.rows)

    def test_exact_counts_and_root_disjoint_numeric_ranges(self):
        self.assertEqual(self.report["examples"], 464)
        self.assertEqual(self.report["pairs"], 232)
        self.assertEqual(
            self.report["by_split"], {"train": 256, "dev": 64, "test": 144}
        )
        root_splits = {}
        for row in self.rows:
            root_splits.setdefault(row["root"], set()).add(row["split"])
            self.assertIn(row["M"], REGIMES[row["split"]]["M"])
            self.assertIn(row["K"], REGIMES[row["split"]]["K"])
        self.assertTrue(all(len(splits) == 1 for splits in root_splits.values()))

    def test_every_negative_violates_only_source_ode(self):
        for row in self.rows:
            check = row["oracle"]
            self.assertTrue(check["product_bound"])
            self.assertTrue(check["denominator"] > 0)
            self.assertEqual(frac(check["product"]),
                             Fraction(check["numerator"], check["denominator"]))
            if row["gold_label"] == "VIOLATES":
                self.assertFalse(check["all_local_gates"])
                self.assertEqual(check["failed_gates"],
                                 [{"window": row["K"] - 1, "gates": ["window_ode"]}])
            else:
                self.assertTrue(check["all_local_gates"])
                self.assertEqual(check["failed_gates"], [])

    def test_source_ode_strictly_stronger_than_weak_envelope(self):
        tight = oracle(4, Fraction(1), [{"I": 1, "before": "1", "after": "4/3"}])
        counterexample = oracle(
            4, Fraction(1), [{"I": 1, "before": "1", "after": "7/5"}]
        )
        self.assertTrue(tight["all_local_gates"])
        self.assertTrue(tight["product_bound"])
        self.assertFalse(counterexample["all_local_gates"])
        self.assertTrue(counterexample["product_bound"])
        self.assertEqual(counterexample["failed_gates"],
                         [{"window": 0, "gates": ["window_ode"]}])

    def test_exact_scale_invariance(self):
        first = oracle(4, Fraction(1), [{"I": 1, "before": "1", "after": "4/3"}])
        scaled = oracle(12, Fraction(1), [{"I": 3, "before": "1", "after": "4/3"}])
        self.assertEqual(first["product"], scaled["product"])
        self.assertEqual(first["sum_dimensionless_cost"],
                         scaled["sum_dimensionless_cost"])
        self.assertEqual(first["gates"], scaled["gates"])

    def test_zero_and_half_budget_boundaries(self):
        zero_cost = oracle(4, Fraction(1), [{"I": 0, "before": "1", "after": "1"}])
        half_cost = oracle(4, Fraction(1), [{"I": 2, "before": "1", "after": "2"}])
        self.assertTrue(zero_cost["all_local_gates"])
        self.assertTrue(half_cost["all_local_gates"])
        self.assertEqual(zero_cost["product"], "1/1")
        self.assertEqual(half_cost["product"], "2/1")

    def test_reject_discontinuous_chains(self):
        with self.assertRaisesRegex(ValueError, "Noncontiguous"):
            oracle(4, Fraction(1), [
                {"I": 1, "before": "1", "after": "4/3"},
                {"I": 1, "before": "2", "after": "8/3"},
            ])

    def test_public_prompt_custody_and_scoring(self):
        tasks = public_rows(self.rows)
        self.assertEqual(len(tasks), 144)
        self.assertTrue(all(set(t) == {"id", "pair_id", "prompt"} for t in tasks))
        self.assertTrue(all("gold_label" not in json.dumps(t) for t in tasks))
        test_rows = [row for row in self.rows if row["split"] == "test"]
        constant = {row["id"]: "SATISFIES" for row in test_rows}
        result = score(self.rows, constant)
        self.assertEqual(result["accuracy"], 0.5)
        self.assertEqual(result["complete_pairs"], 0)
        self.assertEqual(result["test_pairs"], 72)
        exact = {row["id"]: row["gold_label"] for row in test_rows}
        self.assertEqual(score(self.rows, exact)["complete_pairs"], 72)
        self.assertEqual(score(self.rows, exact)["accuracy"], 1)
        with self.assertRaisesRegex(ValueError, "outside frozen"):
            score(self.rows, {"not-in-test": LABELS[0]})
        with self.assertRaisesRegex(ValueError, "Unrecognized"):
            score(self.rows, {test_rows[0]["id"]: "GLOBAL_PDE_SOLVED"})

    def test_manifest_sha_and_prediction_contract(self):
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp)
            receipt = export(out, self.rows)
            self.assertEqual(receipt["seed"], SEED)
            self.assertEqual(receipt["constant_label_baseline"]["accuracy"], 0.5)
            self.assertEqual(len(receipt["sha256"]), 5)
            self.assertEqual(receipt["sha256"], export(out, self.rows)["sha256"])
            expected = {r["id"] for r in self.rows if r["split"] == "test"}
            key = next(iter(expected))
            predictions = out / "predictions.jsonl"
            predictions.write_text(json.dumps({"id": key, "label": "VIOLATES"}) + "\n")
            self.assertEqual(read_predictions(predictions, expected),
                             {key: "VIOLATES"})
            predictions.write_text(
                json.dumps({"id": key, "label": "VIOLATES", "oracle": {}}) + "\n"
            )
            with self.assertRaisesRegex(ValueError, "Leaked"):
                read_predictions(predictions, expected)
            predictions.write_text(
                json.dumps({"id": key, "label": "VIOLATES"}) + "\n" +
                json.dumps({"id": key, "label": "SATISFIES"}) + "\n"
            )
            with self.assertRaisesRegex(ValueError, "Duplicate"):
                read_predictions(predictions, expected)

    def test_deterministic_seed_and_tamper_detection(self):
        self.assertEqual(generate(SEED), self.rows)
        self.assertEqual(len({row["id"] for row in generate(19)}), len(self.rows))
        mutated = [dict(r) for r in self.rows]
        mutated[0]["gold_label"] = (
            "VIOLATES" if mutated[0]["gold_label"] == "SATISFIES" else "SATISFIES"
        )
        with self.assertRaisesRegex(ValueError, "Gold label"):
            check_corpus(mutated)


if __name__ == "__main__":
    unittest.main()

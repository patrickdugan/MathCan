"""BSAR-09: deterministic exact-rational source-window validation corpus.

All arithmetic uses fractions.Fraction, never binary floats or approximations.
This builds a finite-window product audit and intentionally hard negatives:
the final invalid window violates the original BSA-R ODE while still
satisfying the weaker BSAR-08 product-envelope bound.

This is source-level arithmetic, not a PDE simulation or Lean kernel checker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any

SOURCE_COMMIT = "80c62433b0eb671175bd8d6169822d3ebd922b60"
SOURCE_THEOREM = "SweetbrierBSARStep7.step7_leray_quadratic_doubling_closure"
SEED = 2026112209
LABELS = ("SATISFIES", "VIOLATES")
REGIMES = {
    "train": {"M": (4, 6, 8, 10), "K": (1, 2, 3, 4)},
    "dev": {"M": (12, 14), "K": (5, 6)},
    "test": {"M": (16, 18, 20), "K": (7, 8, 9)},
}
REPEATS = 8


def frac(value: Fraction | str | int) -> Fraction:
    return value if isinstance(value, Fraction) else Fraction(value)


def encode(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def _hash(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()[:20]


def _jsonlines(rows: list[dict[str, Any]]) -> bytes:
    return "".join(
        json.dumps(row, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n"
        for row in rows
    ).encode("utf-8")


def oracle(m: int, d0: Fraction, windows: list[dict[str, Any]]) -> dict[str, Any]:
    if m <= 0 or d0 < 0:
        raise ValueError("M must be positive, and d0 must be nonnegative")
    state = d0
    factors = Fraction(1)
    budget = Fraction(0)
    numerator = 1
    denominator = 1
    gates = []
    for step in windows:
        im = step["I"]
        if not isinstance(im, int):
            raise ValueError("Window I must be a nonnegative integer")
        start, end = frac(step["before"]), frac(step["after"])
        if start != state:
            raise ValueError("Noncontiguous window chain")
        gate = {
            "I_nonnegative": im >= 0,
            "next_nonnegative": end >= 0,
            "half_budget": 2 * im <= m,
            "window_ode": m * (end - start) <= im * end,
        }
        gates.append(gate)
        state = end
        numerator *= m + 2 * im
        denominator *= m
        factors *= Fraction(m + 2 * im, m)
        budget += Fraction(im, m)
    return {
        "all_local_gates": all(all(g.values()) for g in gates),
        "failed_gates": [
            {"window": i, "gates": [name for name, passed in g.items() if not passed]}
            for i, g in enumerate(gates) if not all(g.values())
        ],
        "source_ode_all": all(g["window_ode"] for g in gates),
        "product_bound": denominator * state <= numerator * d0,
        "denominator": denominator,
        "numerator": numerator,
        "product": encode(factors),
        "sum_dimensionless_cost": encode(budget),
        "start": encode(d0),
        "final": encode(state),
        "gates": gates,
    }


def _make_pair(split: str, m: int, k: int, repeat: int, seed: int) -> list[dict[str, Any]]:
    rng = random.Random(f"{seed}:{split}:{m}:{k}:{repeat}")
    d0 = Fraction(rng.randrange(1, 12), rng.randrange(1, 8))
    state = d0
    prefix: list[dict[str, Any]] = []
    for index in range(k):
        im = rng.randrange(0, m // 2 + 1)
        if index == k - 1:
            im = rng.randrange(1, m // 2)
        after = state * Fraction(m, m - im)
        prefix.append({"I": im, "before": encode(state), "after": encode(after)})
        state = after
    last = prefix[-1]
    prev = frac(last["before"])
    im = last["I"]
    tight = frac(last["after"])
    weak = prev * Fraction(m + 2 * im, m)
    if not (tight < weak):
        raise AssertionError("Interior I must provide slack between ODE and envelope")
    violated = tight + (weak - tight) / 2
    changed = dict(last)
    changed["after"] = encode(violated)
    negative = prefix[:-1] + [changed]
    identity = f"{SOURCE_COMMIT}:{split}:{m}:{k}:{repeat}"
    pair_id = _hash(identity)
    rows = []
    for label, chain in (("SATISFIES", prefix), ("VIOLATES", negative)):
        check = oracle(m, d0, chain)
        if check["all_local_gates"] != (label == "SATISFIES"):
            raise AssertionError("Oracle label mismatch")
        if not check["product_bound"]:
            raise AssertionError("Hard-negative pair must both satisfy weak product envelope")
        if label == "VIOLATES" and check["failed_gates"] != [
            {"window": k - 1, "gates": ["window_ode"]}
        ]:
            raise AssertionError("Counterexample must violate exactly one ODE premise")
        question = (
            "For these rational BSA-R source windows, decide whether EVERY local ODE "
            "inequality M*(Dnext-Dprev) <= I*Dnext holds, together with "
            "0<=I<=M/2 and Dnext>=0. "
            f"M={m}; D0={encode(d0)}; windows={json.dumps(chain, separators=(',', ':'))}. "
            "Reply SATISFIES or VIOLATES."
        )
        rows.append({
            "id": _hash(identity + ":" + label),
            "pair_id": pair_id,
            "split": split,
            "source_commit": SOURCE_COMMIT,
            "source_theorem": SOURCE_THEOREM,
            "root": identity,
            "M": m,
            "K": k,
            "d0": encode(d0),
            "windows": chain,
            "prompt": question,
            "gold_label": label,
            "oracle": check,
            "evidence_scope": "EXACT_FRACTION_LOCAL_ARITHMETIC_ONLY",
        })
    return rows


def generate(seed: int = SEED) -> list[dict[str, Any]]:
    rows = [
        row
        for split, regime in REGIMES.items()
        for m in regime["M"]
        for k in regime["K"]
        for repeat in range(REPEATS)
        for row in _make_pair(split, m, k, repeat, seed)
    ]
    random.Random(seed).shuffle(rows)
    return rows


def check_corpus(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ids: set[str] = set()
    pairs: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["id"] in ids:
            raise ValueError("Duplicate ID")
        ids.add(row["id"])
        pairs[row["pair_id"]].append(row)
        if row["source_commit"] != SOURCE_COMMIT:
            raise ValueError("Source revision changed")
        if row["K"] != len(row["windows"]):
            raise ValueError("Incorrect window count")
        if row["M"] not in REGIMES[row["split"]]["M"] or row["K"] not in REGIMES[row["split"]]["K"]:
            raise ValueError("Split regime violation")
        result = oracle(row["M"], frac(row["d0"]), row["windows"])
        if result != row["oracle"]:
            raise ValueError("Tampered oracle receipt")
        if row["gold_label"] != ("SATISFIES" if result["all_local_gates"] else "VIOLATES"):
            raise ValueError("Gold label differs from exact arithmetic")
        if not result["product_bound"]:
            raise ValueError("Expected a weak product envelope-consistent example")
    if any(
        len(pair) != 2
        or {x["gold_label"] for x in pair} != set(LABELS)
        or len({x["root"] for x in pair}) != 1
        for pair in pairs.values()
    ):
        raise ValueError("Unmatched label pair")
    counts = dict(Counter(row["split"] for row in rows))
    if counts != {"train": 256, "dev": 64, "test": 144}:
        raise ValueError(f"Unexpected split distribution: {counts}")
    return {
        "source_commit": SOURCE_COMMIT,
        "examples": len(rows),
        "pairs": len(pairs),
        "by_split": counts,
        "ratio_product_bound_valid_for_every_row": True,
        "hard_negative_property": "source ODE violated while weak product bound holds",
        "evidence_scope": "exact finite Fraction evaluation; not a trained model",
    }


def public_rows(rows: list[dict[str, Any]]) -> list[dict[str, str]]:
    return [
        {"id": row["id"], "pair_id": row["pair_id"], "prompt": row["prompt"]}
        for row in sorted(rows, key=lambda x: x["id"])
        if row["split"] == "test"
    ]


def score(rows: list[dict[str, Any]], predicted: dict[str, str]) -> dict[str, Any]:
    test = {row["id"]: row for row in rows if row["split"] == "test"}
    if not set(predicted) <= set(test):
        raise ValueError("Prediction outside frozen test set")
    if any(x not in (*LABELS, "ABSTAIN") for x in predicted.values()):
        raise ValueError("Unrecognized answer label")
    matched = sum(predicted.get(key) == row["gold_label"] for key, row in test.items())
    groups: dict[str, list[str]] = defaultdict(list)
    for key, row in test.items():
        groups[row["pair_id"]].append(key)
    complete = sum(
        all(predicted.get(key) == test[key]["gold_label"] for key in keys)
        for keys in groups.values()
    )
    return {
        "test_examples": len(test),
        "accuracy": matched / len(test),
        "coverage": sum(x in LABELS for x in predicted.values()) / len(test),
        "complete_pairs": complete,
        "test_pairs": len(groups),
    }


def _dump(path: Path, rows: list[dict[str, Any]]) -> str:
    content = _jsonlines(rows)
    path.write_bytes(content)
    return hashlib.sha256(content).hexdigest()


def export(out: Path, rows: list[dict[str, Any]]) -> dict[str, Any]:
    manifest = check_corpus(rows)
    out.mkdir(parents=True, exist_ok=True)
    hashes = {"corpus": _dump(out / "corpus.jsonl", rows)}
    for split in REGIMES:
        hashes[split] = _dump(out / f"{split}.jsonl", [r for r in rows if r["split"] == split])
    hashes["public_test"] = _dump(out / "public_test.jsonl", public_rows(rows))
    control = {row["id"]: "SATISFIES" for row in rows if row["split"] == "test"}
    manifest.update({
        "sha256": hashes,
        "seed": SEED,
        "constant_label_baseline": score(rows, control),
        "custody": "Public test cases are deterministic and not sealed against corpus inspection",
    })
    (out / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return manifest


def read_predictions(path: Path, expected: set[str]) -> dict[str, str]:
    predictions: dict[str, str] = {}
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        row = json.loads(line)
        if {"gold_label", "oracle", "answer"} & set(row):
            raise ValueError(f"Leaked gold or oracle in prediction on line {i}")
        key, label = row.get("id"), row.get("label")
        if key not in expected or not isinstance(key, str):
            raise ValueError(f"Unknown held-out ID on line {i}")
        if key in predictions:
            raise ValueError(f"Duplicate ID on line {i}")
        if label not in (*LABELS, "ABSTAIN"):
            raise ValueError(f"Invalid model label on line {i}")
        predictions[key] = label
    return predictions


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    gen = sub.add_parser("generate")
    gen.add_argument("--output-dir", type=Path, required=True)
    audit = sub.add_parser("audit")
    audit.add_argument("--corpus", type=Path, required=True)
    ev = sub.add_parser("score")
    ev.add_argument("--corpus", type=Path, required=True)
    ev.add_argument("--predictions", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "generate":
        receipt = export(args.output_dir, generate())
    else:
        rows = [json.loads(x) for x in args.corpus.read_text(encoding="utf-8").splitlines() if x]
        manifest = check_corpus(rows)
        if args.command == "score":
            expected = {r["id"] for r in rows if r["split"] == "test"}
            receipt = score(rows, read_predictions(args.predictions, expected))
        else:
            receipt = manifest
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

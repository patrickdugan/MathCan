"""Generate grounded synthetic theorem-boundary examples from six-round BSA-R source.

The source is a pinned *static* theorem catalog. Labels classify claim scope,
not the validity of unexecuted Lean proofs. Holdout by entire research round
and by theorem name. Output is deterministic and safe to rebuild offline.
"""

import argparse
import hashlib
import json
import random
from collections import defaultdict
from pathlib import Path


CATALOG = Path(__file__).with_name("six_round_catalog.json")
SPLIT_PRIORITY = {"train": 0, "dev": 1, "test": 2}


def round_split(path: str) -> str:
    if "Step6" in path:
        return "dev"
    if "Step7" in path:
        return "test"
    return "train"


def generate(catalog: dict, seed: int = 20261122) -> list[dict]:
    assert catalog["source_commit"] == "80c62433b0eb671175bd8d6169822d3ebd922b60"
    source = []
    for group in catalog["rounds"]:
        split = round_split(group["path"])
        for decl in group["declarations"]:
            source.append((split, group["path"], decl))

    # Put repeated helper-theorem names in the latest split only. This prevents
    # declarations such as int_sq_nonneg leaking from train into held-out rounds.
    owner = defaultdict(int)
    for split, _, decl in source:
        owner[decl["name"]] = max(owner[decl["name"]], SPLIT_PRIORITY[split])

    rng = random.Random(seed)
    rows = []
    for split, path, decl in source:
        if SPLIT_PRIORITY[split] != owner[decl["name"]]:
            continue
        theorem = decl["name"]
        statement = decl["signature"]
        preface = ("Source: BSA-R pinned Lean declaration at "
                   + path + ":" + str(decl["line"]) + "\nLean signature: " + statement)
        tasks = [
            ("source_identity",
             "Does the source contain the displayed declaration?",
             "SOURCE_DECLARATION_PRESENT",
             "This exact declaration was transcribed from the pinned source."),
            ("false_global_lift",
             "Does this declaration alone establish unconditional global smoothness for every unforced three-dimensional Navier–Stokes initial datum?",
             "UNSUPPORTED_PDE_LIFT",
             "The declaration provides no theorem over smooth Navier–Stokes solutions and no global PDE a priori estimate."),
            ("false_real_domain",
             "Does its displayed signature itself quantify over real-valued smooth vector fields on the three-torus?",
             "MISSING_ANALYTIC_TYPE_BRIDGE",
             "The source signature does not declare smooth spatial fields or a real-valued PDE solution."),
            ("unrun_kernel",
             "Can this textual signature alone certify that Lean kernel compilation and axiom auditing succeeded?",
             "KERNEL_CHECK_REQUIRED",
             "Kernel checks require actual compilation and inspection beyond reading source text."),
        ]
        if decl["premises"]:
            premise = rng.choice(decl["premises"])
            tasks.extend([
                ("premise_present",
                 "Does the declaration explicitly list a hypothesis named " + premise + "?",
                 "NAMED_PREMISE_PRESENT",
                 "The named hypothesis occurs in the displayed theorem statement."),
                ("premise_erasure",
                 "Can a direct application of this theorem omit providing its hypothesis " + premise + " without obtaining it from context?",
                 "MISSING_PREMISE",
                 "An application requires the specified hypothesis or a proof deriving it."),
            ])
        for template, question, label, reason in tasks:
            ident = hashlib.sha256(f"{path}:{theorem}:{template}".encode()).hexdigest()[:20]
            rows.append({
                "id": ident,
                "split": split,
                "source_commit": catalog["source_commit"],
                "source_path": path,
                "source_line": decl["line"],
                "root": f"{path}:{theorem}",
                "template": template,
                "prompt": preface + "\nClaim to evaluate: " + question,
                "gold_label": label,
                "gold_reason": reason,
                "evidence_type": "STATIC_LEAN_SOURCE_ONLY",
            })
    rng.shuffle(rows)
    return rows


def check_dataset(rows: list[dict]) -> dict:
    by_split = defaultdict(list)
    for row in rows:
        by_split[row["split"]].append(row)
    assert len(rows) == len(set(row["id"] for row in rows))
    names = {}
    for split, examples in by_split.items():
        for ex in examples:
            name = ex["root"].split(":")[-1]
            if name in names:
                assert names[name] == split, f"theorem-name leakage: {name}"
            names[name] = split
    labels = {ex["gold_label"] for ex in rows}
    expected = {"SOURCE_DECLARATION_PRESENT", "UNSUPPORTED_PDE_LIFT",
                "MISSING_ANALYTIC_TYPE_BRIDGE", "KERNEL_CHECK_REQUIRED",
                "NAMED_PREMISE_PRESENT", "MISSING_PREMISE"}
    assert labels == expected
    assert all(by_split[k] for k in ("train", "dev", "test"))
    return {"examples": len(rows), "split_counts": {k: len(v) for k, v in by_split.items()},
            "label_counts": {k: sum(ex["gold_label"] == k for ex in rows) for k in sorted(labels)},
            "unique_roots": len(set(r["root"] for r in rows))}


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--catalog", type=Path, default=CATALOG)
    p.add_argument("--output-dir", type=Path, required=True)
    p.add_argument("--seed", type=int, default=20261122)
    args = p.parse_args(argv)
    catalog = json.loads(args.catalog.read_text(encoding="utf-8"))
    examples = generate(catalog, seed=args.seed)
    manifest = check_dataset(examples)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for split in ("train", "dev", "test"):
        path = args.output_dir / f"bsar_boundary_{split}.jsonl"
        with path.open("w", encoding="utf-8") as f:
            for row in examples:
                if row["split"] == split:
                    f.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    manifest["source_commit"] = catalog["source_commit"]
    manifest["seed"] = args.seed
    manifest["meaning"] = "synthetic theorem-scope labels; no model training or kernel verification"
    (args.output_dir / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

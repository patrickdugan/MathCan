"""Exact count of matched same-basin donor triplets for BPD-COL-02."""
from collections import Counter, defaultdict
from math import gcd
import json
from pathlib import Path
import argparse
from .collatz_core import analyze, modular_labels


def branch(n):
    return 3 if n % 4 == 1 else 1


def trace_partition(core, q):
    part = {n: (q[n % core.d], branch(n)) for n in core.states}
    while True:
        ids = {}
        new = {}
        for n in core.states:
            key = (part[n], part[core.successors[n]])
            new[n] = ids.setdefault(key, len(ids))
        if len(ids) == len(set(part.values())):
            return new
        part = new


def count_root(d):
    core = analyze(d)
    q = modular_labels(d)
    stable = trace_partition(core, q)
    result = {"d": d, "states": len(core.states), "horizons": {}}
    for h in (1, 2):
        groups = defaultdict(list)
        for n in core.states:
            x = n
            for _ in range(h):
                x = core.successors[x]
            groups[(q[n % d], branch(n), core.basin[n])].append((branch(x), stable[n]))
        ordinary = exact_sham = 0
        for group in groups.values():
            label = Counter(y for y, _ in group)
            trace = Counter(p for _, p in group)
            for y, p in group:
                ordinary += label[4-y] * (label[y]-1)
                exact_sham += label[4-y] * (trace[p]-1)
        result["horizons"][str(h)] = {"ordinary_triplets": ordinary, "infinite_sham_triplets": exact_sham}
    return result


def census():
    rows = [count_root(d) for d in range(1, 1026, 4) if gcd(d, 6) == 1]
    agg = {}
    eligible = {}
    for h in ("1", "2"):
        ordinary = [r for r in rows if r["horizons"][h]["ordinary_triplets"]]
        strong = [r for r in rows if r["horizons"][h]["infinite_sham_triplets"]]
        eligible[h] = {r["d"] for r in strong}
        agg[h] = {
            "parameters": len(rows), "ordinary_roots": len(ordinary), "infinite_sham_roots": len(strong),
            "ordinary_triplets": sum(r["horizons"][h]["ordinary_triplets"] for r in rows),
            "infinite_sham_triplets": sum(r["horizons"][h]["infinite_sham_triplets"] for r in rows),
        }
    return {"scope": "complete exposed development core; ordered distinct recipient/effect/sham roles",
            "states": sum(r["states"] for r in rows), "horizons": agg,
            "infinite_sham_root_union": len(eligible["1"] | eligible["2"]),
            "infinite_sham_root_intersection": len(eligible["1"] & eligible["2"]), "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    result = census()
    if args.check:
        expected = json.loads(args.check.read_text())
        actual = {k: result[k] for k in expected}
        if actual != expected:
            raise SystemExit("donor census mismatch")
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()

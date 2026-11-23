"""Read-only free-plan inventory and connected four-qubit snapshots."""
import argparse
from datetime import datetime, timezone
from itertools import combinations
from math import isfinite
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from ibm_qpu_03.backend_snapshot import NATIVE, capture, open_account, write_json


def candidate_layouts(target):
    readout = {q[0]: prop for q, prop in target["measure"].items()
               if q and prop and prop.error is not None and prop.duration is not None}
    links = {}
    neighbors = {q: set() for q in readout}
    for name in sorted(set(NATIVE) & set(target.operation_names)):
        for pair, prop in target[name].items():
            if not pair or not prop or prop.error is None or prop.duration is None:
                continue
            a, b = pair
            if a not in readout or b not in readout:
                continue
            key = tuple(sorted(pair))
            score = prop.error + 4000 * prop.duration
            if key not in links or score < links[key][0]:
                links[key] = (score, name, prop.error, prop.duration)
            neighbors[a].add(b)
            neighbors[b].add(a)
    subsets = {frozenset([q]) for q in readout}
    for _ in range(3):
        subsets = {group | {b} for group in subsets for a in group for b in neighbors[a] - group}
    ranked = []
    for group in subsets:
        if not all(target.qubit_properties[q].t1 and target.qubit_properties[q].t2 for q in group):
            continue
        native = [(links[pair], pair) for pair in combinations(sorted(group), 2) if pair in links]
        # A three-edge connected spanning tree determines the basic routing cost.
        possible = [choice for choice in combinations(native, 3)
                    if len({q for _, pair in choice for q in pair}) == 4]
        tree = min(possible, key=lambda span: sum(edge[0] for edge, _ in span))
        score = 20 * sum(edge[0] for edge, _ in tree) + sum(readout[q].error for q in group)
        # Prioritize an interior physical qubit for the internal mode.
        layout = sorted(group, key=lambda q: (len(neighbors[q] & group), q))
        ranked.append({"physical_xyz": layout, "score": score,
                       "native_edges": [{"qubits": list(pair), "gate": edge[1],
                                         "error": edge[2], "duration_s": edge[3]}
                                        for edge, pair in native]})
    return sorted(ranked, key=lambda row: (row["score"], row["physical_xyz"]))


def compact_snapshot(backend, layout):
    snapshot = capture(backend, layout)
    snapshot["coherence_s"] = [
        [backend.target.qubit_properties[q].t1, backend.target.qubit_properties[q].t2]
        for q in layout["physical_xyz"]
    ]
    return snapshot


def inventory(config_path):
    service, crn = open_account(config_path)
    usage = service.usage()
    seconds = usage.get("usage_remaining_seconds")
    ru = usage.get("usage_remaining_ru")
    candidates = [v for v in (seconds, 60*ru if isinstance(ru, (float, int)) else None)
                  if isinstance(v, (int, float)) and isfinite(v)]
    if not candidates or service.active_instance() != crn:
        raise RuntimeError("Open Plan balance is unavailable")
    account = {"plan": "open", "free_qpu_seconds": 0 if usage.get("usage_limit_reached")
               else max(0, min(candidates)), "checked_utc": datetime.now(timezone.utc).isoformat()}
    layouts = []
    for backend in service.backends(operational=True, simulator=False, instance=crn):
        ranked = candidate_layouts(backend.target)
        if ranked:
            layouts.append((ranked[0]["score"], backend.name, backend, ranked))
    if not layouts:
        raise RuntimeError("no connected calibrated four-qubit layout")
    layouts.sort(key=lambda row: row[:2])
    _, _, backend, ranked = layouts[0]
    return {"source": "live_read_only", "account": account, "qpu_submitted": False,
            "device_candidates": [{"backend": name, "layout": candidates[0]}
                                  for _, name, _, candidates in layouts],
            "snapshots": [compact_snapshot(backend, layout) for layout in ranked[:2]]}


def historical():
    from qiskit_ibm_runtime.fake_provider import FakeFez
    backend = FakeFez()
    return {"source": "historical_fake_backend", "account": None, "qpu_submitted": False,
            "snapshots": [compact_snapshot(backend, row) for row in candidate_layouts(backend.target)[:2]]}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--credential-file")
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    try:
        result = inventory(args.credential_file) if args.credential_file else historical()
    except Exception as exc:
        p.exit(1, f"Calibration metadata unavailable ({type(exc).__name__}).\n")
    write_json(args.output, result)
    print(result["source"], result["account"], result["snapshots"][0]["backend"])


if __name__ == "__main__":
    main()

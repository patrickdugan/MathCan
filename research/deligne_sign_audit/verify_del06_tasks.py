"""Independent exact-arithmetic receipt for DEL-06 DataGoblin tasks.

Every task is checked by arithmetic on matrices, tensor spectra or the
explicit hypothesis being mutated. These are finite shadows, not etale
cohomology or a full Lean formalization.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import json

from research.deligne_sign_audit.geometry_trace import (
    mat, powered_trace_splitting, tensor_power_trace,
    tensor_spectrum, twist_trace_pair, signed_power_remainder,
    kunneth_lowest_degree_paths,
)

DATA = Path(__file__).with_name("del06_tasks.jsonl")
EXPECTED = {
    "boundary_ok": 20,
    "lower_block_mutant": 10,
    "tate_ok": 10,
    "tensor_ok": 12,
    "kunneth_vanishing_mutant": 6,
    "virtual_trace_mutant": 6,
    "sign_parity": 8,
}

def verify():
    cases = [json.loads(line) for line in
             DATA.read_text(encoding="utf-8").splitlines() if line.strip()]
    if len(cases) != 72 or len(set(t["id"] for t in cases)) != 72:
        raise AssertionError("DEL-06 corpus must contain 72 unique rows")
    counts = Counter()
    for t in cases:
        kind = t["kind"]
        counts[kind] += 1
        if kind in ("boundary_ok", "lower_block_mutant"):
            K, Qmat, mix = mat(t["K"]), mat(t["Q"]), mat(t["mix"])
            lower = mat(t["lower"]) if kind == "lower_block_mutant" else None
            lhs, rhs = powered_trace_splitting(K, Qmat, mix,
                                               t["n"], lower)
            assert lhs == Q(t["expected_trace"]), t["id"]
            if kind == "boundary_ok":
                assert lhs == rhs and t["label"] == "pass", t["id"]
            else:
                assert rhs == Q(t["expected_diagonal_trace"]), t["id"]
                assert lhs != rhs and t["label"] == "reject", t["id"]
        elif kind == "tate_ok":
            actual, expected = twist_trace_pair(t["r"], t["eigenvalues"],
                                                 t["n"])
            assert actual == expected == Q(t["expected_trace"]), t["id"]
            wrong = Q(t["r"]) * sum((Q(x)**t["n"] for x in t["eigenvalues"]),Q(0))
            assert actual != wrong and t["label"] == "pass", t["id"]
        elif kind == "tensor_ok":
            actual, expected = tensor_power_trace(t["eigenvalues"], t["k"], t["n"])
            assert actual == expected == Q(t["expected_trace"]), t["id"]
            vals = tensor_spectrum(tuple(map(Q,t["eigenvalues"])),t["k"])
            assert Q(t["expected_target"]) in vals, t["id"]
            assert Q(t["distinguished"])**t["k"] in vals, t["id"]
            assert t["label"] == "pass"
        elif kind == "kunneth_vanishing_mutant":
            assert sum(t["degrees"]) == t["expected_total"] == t["d"]*t["k"]
            assert any(j < t["d"] for j in t["degrees"])
            assert tuple(t["degrees"]) not in kunneth_lowest_degree_paths(t["d"],t["k"])
            assert t["label"] == "reject"
        elif kind == "virtual_trace_mutant":
            a = Q(t["alpha"])
            trace = sum((m*a**t["n"] for m in t["multiplicities"]),Q(0))
            assert trace == Q(t["expected_trace"]) == 0
            assert any(m < 0 for m in t["multiplicities"])
            assert t["label"] == "reject"
        elif kind == "sign_parity":
            K,Qmat,mix,L = (mat(t[x]) for x in ("K","Q","mix","L"))
            signed = signed_power_remainder(K,Qmat,mix,L,[],t["n"])
            sign = (-1)**(t["D"]-1)
            assert signed == Q(t["expected_signed"])
            assert sign * Q(t["expected_remainder"]) == signed
            assert t["label"] == "pass"
        else:
            raise AssertionError(f"unknown case {kind}")
    if dict(counts) != EXPECTED:
        raise AssertionError((counts,EXPECTED))
    return counts

if __name__ == "__main__":
    counts = verify()
    print("DEL-06 exact mutation receipts:",sum(counts.values()))
    print(dict(sorted(counts.items())))

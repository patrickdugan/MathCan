#!/usr/bin/env python3
"""Exact finite slices of independent operator-theory countermodels.

These examples audit implications about dimension, trace and gluing.
They do not implement a gravitational theory.
"""
from fractions import Fraction
import argparse
import hashlib
import json
import math
from pathlib import Path


def cutoff_ordering():
    """Finite slices of strongly exhausting, order-dependent normalized traces."""
    rows = []
    for cycle_length in (2, 3, 5, 17):
        expected = Fraction(2 * (cycle_length - 1), 2 * cycle_length - 1)
        for cycle_count in (1, 2, 8, 32):
            indices = []
            for k in range(cycle_count):
                indices.extend(
                    2 * ((cycle_length - 1) * k + j)
                    for j in range(cycle_length - 1)
                )
                indices.append(2 * k + 1)
            assert len(indices) == len(set(indices)) == cycle_length * cycle_count
            # Every coordinate below 2K occurs, so the projections exhaust the
            # standard basis as K increases, for each fixed cycle length.
            assert set(range(2 * cycle_count)).issubset(indices)
            weights = [Fraction(1) if i % 2 == 0 else Fraction(1, 2) for i in indices]
            even_weight = sum((w for i, w in zip(indices, weights) if i % 2 == 0), Fraction())
            total_weight = sum(weights, Fraction())
            probability = even_weight / total_weight
            assert total_weight == Fraction(cycle_count * (2 * cycle_length - 1), 2)
            assert probability == expected
            rows.append({
                "cycle_length": cycle_length,
                "cycle_count": cycle_count,
                "rank": len(indices),
                "contains_initial_coordinates": 2 * cycle_count,
                "total_weight_exact": str(total_weight),
                "even_observable_probability_exact": str(probability),
            })
    assert len({row["even_observable_probability_exact"] for row in rows}) == 4
    return {
        "area_eigenvalues": {"even": "0", "odd": "log(2)"},
        "weight_eigenvalues": {"even": "1", "odd": "1/2"},
        "uniform_weight_lower_bound": "1/2",
        "closed_weight_trace": "infinite",
        "strong_exhaustion": "every coordinate below 2K lies in P_(K,r)",
        "limit_probability_formula": "2(r-1)/(2r-1)",
        "conclusion": "strong exhaustion alone does not determine a normalized trace limit",
        "rows": rows,
    }


def source_hashes(lean_source=None):
    script_path = Path(__file__).resolve()
    if lean_source is None:
        candidates = (
            script_path.parent / "NullConeTraceBound.lean",
            script_path.parents[2] / "MathCan" / "NullConeTraceBound.lean",
        )
        lean_source = next((p for p in candidates if p.is_file()), None)
        if lean_source is None:
            raise FileNotFoundError("NullConeTraceBound.lean was not found; pass --lean-source PATH")
    lean_source = Path(lean_source).resolve()
    return {
        "operator_countermodels.py": hashlib.sha256(script_path.read_bytes()).hexdigest(),
        "NullConeTraceBound.lean": hashlib.sha256(lean_source.read_bytes()).hexdigest(),
    }


def receipt(lean_source=None):
    geometric = []
    geometric_display = []
    matched_charges = []
    for n in (4, 8, 16, 32, 64):
        weights = [Fraction(1, 2 ** k) for k in range(1, n + 1)]
        trace = sum(weights, Fraction())
        first_moment = sum((k + 1) * p for k, p in enumerate(weights))
        purity_raw = sum((p * p for p in weights), Fraction())
        assert trace == 1 - Fraction(1, 2**n)
        assert first_moment == 2 - Fraction(n + 2, 2**n)
        assert purity_raw == (1 - Fraction(1, 4**n)) / 3
        purity = purity_raw / (trace * trace)
        entropy = math.log(float(trace)) + math.log(2) * float(first_moment / trace)
        geometric.append({
            "rank": n,
            "trace_exact": str(trace),
            "normalized_first_moment_exact": str(first_moment / trace),
            "normalized_purity_exact": str(purity),
            "effective_dimension_exact": str(1 / purity),
            "entropy_nats_expression": f"log({trace}) + ({first_moment / trace}) * log(2)",
            "minimum_eigenvalue_exact": str(weights[-1] / trace),
        })
        geometric_display.append({
            "rank": n,
            "effective_dimension": float(1 / purity),
            "entropy_nats": entropy,
        })
    for cutoff in (1, 2, 4, 8, 16):
        charges = range(-cutoff, cutoff + 1)
        exact = sum(1 for a in charges for b in charges if a + b == 0)
        assert exact == 2 * cutoff + 1
        matched_charges.append({
            "charge_cutoff": cutoff,
            "ambient_dimension": (2 * cutoff + 1) ** 2,
            "physical_dimension": exact,
            "compression_ratio_exact": str(Fraction((2 * cutoff + 1) ** 2, exact)),
        })
    exact = {
        "scope": "exact finite slices; infinite conclusions have analytic proofs in audit_notes.md",
        "geometric_state": geometric,
        "infinite_limits": {
            "rank": "countably infinite",
            "trace": "1",
            "entropy_nats": "2 log(2)",
            "purity": "1/3",
            "effective_dimension": "3",
            "spectral_infimum": "0",
        },
        "integer_charge_matching": matched_charges,
        "identity_sewing": {
            "partial_vector_squared_norm": "N",
            "normalizable_transition_amplitudes": "bounded by product of input norms",
            "identity_trace": "infinite",
        },
        "cutoff_ordering": cutoff_ordering(),
    }
    return {
        "schema_version": "NCG-AUDIT-01",
        "source_sha256": source_hashes(lean_source),
        "exact": exact,
        "illustrative_values": {
            "replay_policy": "informational floating values; excluded from canonical --check",
            "geometric_state": geometric_display,
            "ordering_probability": [
                {
                    "cycle_length": row["cycle_length"],
                    "probability": float(Fraction(row["even_observable_probability_exact"])),
                }
                for row in exact["cutoff_ordering"]["rows"]
                if row["cycle_count"] == 1
            ],
        },
    }


def canonical_part(value):
    """Only exact values and source hashes participate in the replay gate."""
    return {key: value[key] for key in ("schema_version", "source_sha256", "exact")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group()
    target.add_argument("--output", type=Path, help="write the receipt to this JSON path")
    target.add_argument("--check", type=Path, help="replay exact fields and source hashes against this receipt")
    parser.add_argument("--lean-source", type=Path, help="explicit path to the Lean candidate")
    args = parser.parse_args()
    actual = receipt(args.lean_source)
    if args.check:
        expected = json.loads(args.check.read_text(encoding="utf-8"))
        if canonical_part(actual) != canonical_part(expected):
            raise SystemExit("FAIL: canonical receipt or source hashes differ")
        print("PASS: exact receipt and source hashes match; illustrative floats are excluded")
        return
    serialized = json.dumps(actual, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized, encoding="utf-8")
        print(f"Wrote {args.output}")
    else:
        print(serialized, end="")


if __name__ == "__main__":
    main()

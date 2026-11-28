"""DEL-09 executable verifier for 96 finite-extension and chart mutation tasks."""
from collections import Counter
from pathlib import Path
import json

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del09_oracle import (
    common_subfield_degree, polynomial_open_frobenius_gap,
    injective_graph_certificate, omit_base_coordinate_mutant,
    affine_chart_contains, affine_normalization,
    source_geometry_tangency_mutant, validate_ambient_field,
)

DATA = Path(__file__).with_name("del09_tasks.jsonl")
EXPECTED = {
    "common_subfield":24,
    "extension_required":18,
    "projective_graph":16,
    "missing_base_coordinates":12,
    "point_at_infinity":12,
    "zero_fixed_coefficient":8,
    "tangent_restriction_mutant":6,
}


def verify():
    cases = [json.loads(line) for line in
             DATA.read_text(encoding="utf-8").splitlines()
             if line.strip()]
    assert len(cases)==96, len(cases)
    assert len({row["id"] for row in cases})==96
    counts=Counter()
    for row in cases:
        kind=row["kind"]
        counts[kind]+=1
        field=validate_ambient_field(row["field"])
        if kind=="common_subfield":
            e,order=common_subfield_degree(field,row["coefficients"])
            assert e==row["expected_degree"],row["id"]
            assert order==row["expected_order"],row["id"]
            assert field.degree % e == 0 and row["label"]=="finite_extension"
        elif kind=="extension_required":
            base,ex=polynomial_open_frobenius_gap(field)
            assert len(base)==row["base_count"]==field.p
            assert len(ex)==row["open_count"]==field.q-field.p
            assert row["base_element"] in base
            assert row["outside_element"] in ex
            assert row["label"]=="extension_required"
        elif kind=="projective_graph":
            count,max_fiber=injective_graph_certificate(
                field,row["a"],row["b"])
            assert count==row["expected_fibers"]==field.q
            assert max_fiber==row["expected_max_fiber"]==1
            assert row["label"]=="immersion_shadow"
        elif kind=="missing_base_coordinates":
            count,original=omit_base_coordinate_mutant(field)
            assert count==row["expected_collapsed"]==1
            assert original==row["expected_original"]==field.p
            assert row["label"]=="nonimmersion_mutant"
        elif kind=="point_at_infinity":
            assert not affine_chart_contains(row["coordinates"])
            assert row["coordinates"][1]!=0
            assert row["label"]=="outside_affine_chart"
        elif kind=="zero_fixed_coefficient":
            try: affine_normalization(
                field,row["coefficients"],row["scalar"])
            except ValueError:
                assert row["label"]=="reject_normalization"
            else:
                raise AssertionError(f"{row['id']} admitted zero scalar")
        elif kind=="tangent_restriction_mutant":
            assert source_geometry_tangency_mutant(field)==(
                True,True,True,True),row["id"]
            assert row["label"]=="reject_smoothness_transfer"
        else:
            raise AssertionError(f"unknown task variant: {kind}")
    assert counts==EXPECTED,counts
    return counts


if __name__=="__main__":
    counts=verify()
    print(f"DEL-09 verified proof-repair cases: {sum(counts.values())}/96")
    print(dict(sorted(counts.items())))

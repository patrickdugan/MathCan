"""DEL-08 independent exact verifier for 80 fixed-chart proof-repair tasks."""
from collections import Counter
from pathlib import Path
import json

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del08_oracle import (
    check_normalized_zero_set,
    normalize_hyperplane,
    conic_good,
    conic_singular,
    frobenius_gap,
    tangent_line_restriction_mutant,
    graph_nonimmersion_collision,
)

DATA = Path(__file__).with_name("del08_tasks.jsonl")
EXPECTED = {
    "chart_normalization":24,
    "zero_last_coefficient":8,
    "smooth_conic":12,
    "singular_conic":12,
    "finite_extension_needed":9,
    "tangent_incidence_count":7,
    "ambient_tangent_restriction":4,
    "graph_coordinates_not_surjective":4,
}


def verify():
    cases = [json.loads(s) for s in DATA.read_text(encoding="utf-8").splitlines()
             if s.strip()]
    assert len(cases)==80
    assert len({c["id"] for c in cases}) == len(cases)
    counts=Counter()
    for row in cases:
        kind=row["kind"]
        counts[kind]+=1
        if kind=="tangent_incidence_count":
            d,m = row["D"],row["M"]
            assert d<m and d+(m-d-1)==m-1==row["expectedBadBound"]
            assert row["label"]=="pass_arithmetic_only"
            continue
        f=FIELDS[row["field"]]
        if kind=="chart_normalization":
            a,b=check_normalized_zero_set(
                f, row["a"],row["last"],row["c"],
                row["fixed"],row["z"])
            assert a and b and row["label"]=="pass",row["id"]
        elif kind=="zero_last_coefficient":
            try:
                normalize_hyperplane(f,row["a"],row["last"],row["c"])
            except ValueError:
                assert row["label"]=="reject_chart"
            else:
                raise AssertionError(f"{row['id']} accepted zero coefficient")
        elif kind in ("smooth_conic","singular_conic"):
            a,b,c=(row[x] for x in ("a","b","c"))
            singular,gradient=conic_singular(f,a,b,c)
            assert gradient==(0,0),row["id"]
            assert singular != conic_good(f,a,b,c),row["id"]
            if kind=="smooth_conic":
                assert not singular and row["label"]=="pass",row["id"]
            else:
                assert singular and row["label"]=="reject_smoothness",row["id"]
        elif kind=="finite_extension_needed":
            base_zero,count,outside=frobenius_gap(f)
            assert base_zero and count==row["expectedOutside"],row["id"]
            assert f.sub(f.pow(row["baseElement"],f.p),
                         row["baseElement"])==0,row["id"]
            assert outside and row["label"]=="extension_required",row["id"]
        elif kind=="ambient_tangent_restriction":
            on_level,ambient_regular,restricted_singular=(
                tangent_line_restriction_mutant(f))
            assert on_level and ambient_regular and restricted_singular
            assert row["label"]=="reject_smoothness_transfer"
        elif kind=="graph_coordinates_not_surjective":
            distinct,collision=graph_nonimmersion_collision(f)
            assert distinct and collision
            assert row["label"]=="reject_closed_immersion"
        else:
            raise AssertionError(kind)
    assert counts==EXPECTED,(counts,EXPECTED)
    return counts


if __name__=="__main__":
    counts=verify()
    print(f"DEL-08 exact finite/chart cases verified: {sum(counts.values())}/80")
    print(dict(sorted(counts.items())))

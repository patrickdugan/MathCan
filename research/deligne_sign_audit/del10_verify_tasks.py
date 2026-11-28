"""DEL-10 exact verifier for polynomial nonvanishing and degree budgets."""
from collections import Counter
from pathlib import Path
import json

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del10_oracle import (
    exact_case, linear_term, constant, frobenius_gap_terms,
    high_degree_nonzero_terms,
)

DATA=Path(__file__).with_name("del10_tasks.jsonl")
EXPECTED={
  "valid_linear_chart":32,
  "valid_two_coordinate_F2":8,
  "frobenius_vanishes_all":9,
  "extension_repairs_open":6,
  "high_degree_nonzero":10,
  "zero_polynomial":8,
  "conflicting_F2_opens":8,
}


def materialize(row):
    field=FIELDS[row["field"]]
    kind=row["kind"]
    if kind=="valid_linear_chart":
        a,b=row["a"],row["b"]
        return [
          linear_term(field,a,0,2),
          linear_term(field,b,0,2),
          linear_term(field,0,1,2),
        ]
    if kind=="valid_two_coordinate_F2":
        return [
          linear_term(field,0,0,2),
          linear_term(field,0,1,2),
          constant(field,1,2),
        ]
    if kind=="frobenius_vanishes_all":
        q=field.q
        return [[(1,[q]),(field.neg(1),[1])]]
    if kind=="extension_repairs_open":
        return [frobenius_gap_terms(field)]
    if kind=="high_degree_nonzero":
        return [high_degree_nonzero_terms(field)]
    if kind=="zero_polynomial":
        return [[(0,[0])]]
    if kind=="conflicting_F2_opens":
        return [
          linear_term(field,0,0,1),
          linear_term(field,1,0,1),
          constant(field,1,1),
        ]
    raise ValueError("unknown case "+kind)


def verify():
    cases=[json.loads(x) for x in DATA.read_text(encoding="utf-8").splitlines()
           if x.strip()]
    if len(cases)!=81 or len({r["id"] for r in cases})!=len(cases):
        raise AssertionError("DEL-10 expects 81 unique labeled tasks")
    tally=Counter()
    for row in cases:
        kind=row["kind"]
        tally[kind]+=1
        field=FIELDS[row["field"]]
        receipt=exact_case(row["field"],materialize(row),row["n"])
        assert receipt["strict_degree_gate"]==row["expected_degree_gate"],row["id"]
        assert receipt["exists"]==row["expected_exists"],row["id"]
        if receipt["strict_degree_gate"] and receipt["nonzero_polynomials"]:
            assert receipt["exists"],(row["id"],"violates Nullstellensatz implication")
        if kind in ("valid_linear_chart","valid_two_coordinate_F2"):
            assert len(receipt["polynomials"])==3
            assert receipt["witness"] is not None
            assert row["label"]=="pass"
        elif kind=="frobenius_vanishes_all":
            assert receipt["nonzero_polynomials"]
            assert receipt["degrees"]==(field.q,)
            assert row["label"]=="reject_degree"
        elif kind=="extension_repairs_open":
            base=exact_case(row["base_field"],
                [[(1,[field.p]),(FIELDS[row["base_field"]].neg(1),[1])]],1)
            assert not base["exists"]
            assert receipt["exists"] and receipt["strict_degree_gate"]
            assert row["label"]=="extension_point"
        elif kind=="high_degree_nonzero":
            assert receipt["exists"] and not receipt["strict_degree_gate"]
            assert row["label"]=="sufficient_not_necessary"
        elif kind=="zero_polynomial":
            assert not receipt["nonzero_polynomials"]
            assert not receipt["exists"]
            assert row["label"]=="reject_zero_poly"
        elif kind=="conflicting_F2_opens":
            assert receipt["nonzero_polynomials"]
            assert not receipt["exists"]
            assert row["label"]=="reject_common_open"
        else:
            raise AssertionError(kind)
    assert tally==EXPECTED,tally
    return tally

if __name__=="__main__":
    counts=verify()
    print("DEL-10 exact good-open witnesses verified:",sum(counts.values()))
    print(dict(sorted(counts.items())))

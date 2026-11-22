"""DEL-14 exact verifier for the sharp conic Jacobian ideal criterion."""
from collections import Counter
from pathlib import Path
import json

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del12_oracle import conic_polynomial, evaluate
from research.deligne_sign_audit.del13_oracle import (
    field_oracle, wrong_sign_certificate,
)

DATA=Path(__file__).with_name("del14_tasks.jsonl")
EXPECTED={"unit_ideal":24,"proper_ideal":24,
          "shifted_singular_point":12,"wrong_sign":12}


def verify():
    rows=[json.loads(x) for x in DATA.read_text(encoding="utf-8").splitlines() if x.strip()]
    if len(rows)!=72 or len({x["id"] for x in rows})!=72:
        raise AssertionError("Expected 72 unique DEL-14 cases")
    counts=Counter()
    for r in rows:
        kind=r["kind"]
        counts[kind]+=1
        f=FIELDS[r["field"]]
        a,b,c=(r[k] for k in ("a","b","c"))
        receipt=field_oracle(r["field"],a,b,c)
        self_top=receipt["unit_if_nonzero"]
        singular=receipt["singular_if_zero"]
        assert receipt["identity"],r["id"]
        assert self_top == r["expected_ideal_top"],r["id"]
        assert singular == r["expected_eval_kernel"],r["id"]
        assert self_top == (receipt["delta"]!=0),r["id"]
        assert singular == (receipt["delta"]==0),r["id"]
        if kind=="unit_ideal":
            assert r["label"]=="global_unit"
            assert receipt["unit_certificate"]["unit_identity"]
        elif kind=="proper_ideal":
            assert r["label"]=="proper_eval_witness"
            assert receipt["unit_certificate"] is None
            assert receipt["singular_obstruction"]["generator_evaluations"]==(0,0,0)
        elif kind=="shifted_singular_point":
            assert r["label"]=="evaluate_shifted_point"
            origin_value=evaluate(f,conic_polynomial(f,a,b,c),0,0)
            assert origin_value!=0 and not r["expected_origin_kernel"]
            assert receipt["singular_obstruction"]["singular_point"]==(f.neg(b),f.neg(a))
        elif kind=="wrong_sign":
            assert r["label"]=="reject_wrong_discriminant"
            assert r["expected_wrong_sign_zero"]
            assert wrong_sign_certificate(f,a,b,c)==0
            assert receipt["delta"]!=0
        else:
            raise AssertionError(kind)
    assert counts==EXPECTED,counts
    return counts


if __name__=="__main__":
    counts=verify()
    print("DEL-14 exact sharp Jacobian cases verified:",sum(counts.values()))
    print(dict(sorted(counts.items())))

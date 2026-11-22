"""DEL-12 deterministic verifier for 80 true-derivative Jacobian tasks."""
from collections import Counter
from pathlib import Path
import json

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del12_oracle import (
    derivative_conic_certificate, critical_point,
    inseparable_frobenius_square, tangent_line_counterexample,
    evaluate, discriminant,
)

DATA=Path(__file__).with_name("del12_tasks.jsonl")
EXPECTED={
    "symbolic_derivative":32,
    "actual_critical_point":24,
    "swapped_gradient_mutant":8,
    "inseparable_square":8,
    "tangent_restriction":8,
}


def verify():
    rows=[json.loads(s) for s in DATA.read_text(encoding="utf-8").splitlines()
          if s.strip()]
    assert len(rows)==80 and len({r["id"] for r in rows})==80
    counts=Counter()
    for row in rows:
        kind=row["kind"]
        counts[kind]+=1
        f=FIELDS[row["field"]]
        if kind=="symbolic_derivative":
            r=derivative_conic_certificate(f,*(
              row[k] for k in ("a","b","c","x","y")))
            assert r["symbolic_dx_ok"]==row["expected_dx_correct"]
            assert r["symbolic_dy_ok"]==row["expected_dy_correct"]
            assert r["dx_value"]==r["expected_dx"]
            assert r["dy_value"]==r["expected_dy"]
            assert row["label"]=="pass"
        elif kind=="actual_critical_point":
            x,y,r=critical_point(
                f,row["a"],row["b"],row["c"])
            assert r["dx_value"]==r["dy_value"]==0
            assert r["value"]==discriminant(
                f,row["a"],row["b"],row["c"])==0
            assert row["expected_discriminant_zero"]
            assert row["label"]=="singular"
        elif kind=="swapped_gradient_mutant":
            a,b,c=row["a"],row["b"],row["c"]
            x,y,r=critical_point(f,a,b,c)
            assert not r["dx_value"] and not r["dy_value"]
            wrong_dx=f.add(y,b)
            assert wrong_dx!=0 and row["expected_swapped_dx_nonzero"]
            assert row["expected_true_gradient_zero"]
            assert row["label"]=="reject_swap"
        elif kind=="inseparable_square":
            P,dx=inseparable_frobenius_square(f,row["c"])
            assert not dx and row["expected_derivative_zero"]
            root=0 if row["c"]==0 else 1
            assert evaluate(f,P,root,0)==0
            assert row["label"]=="reject_naive_separability"
        elif kind=="tangent_restriction":
            r=tangent_line_counterexample(f)
            assert r["ambient_on_level"]
            assert r["line_contains_point"]
            assert r["ambient_gradient_nonzero"]==row["expected_ambient_regular"]
            assert r["restricted_point_on_level"]
            assert r["restricted_derivative_zero"]==row["expected_restricted_singular"]
            assert row["label"]=="reject_smooth_transfer"
        else:
            raise AssertionError(kind)
    assert counts==EXPECTED,counts
    return counts

if __name__=="__main__":
    counts=verify()
    print("DEL-12 polynomial-derivative oracle:",sum(counts.values()),"verified")
    print(dict(sorted(counts.items())))

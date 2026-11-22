"""DEL-11 verifier: exact elimination of the critical-point incidence."""
from collections import Counter
from pathlib import Path
import json

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del11_oracle import (
    bad_discriminant, parameter_is_bad,
    critical_point, brute_force_critical_points,
    wrong_plus_discriminant, cross_coupled_discriminant,
)

DATA=Path(__file__).with_name("del11_tasks.jsonl")
EXPECTED={
    "critical_exact":32,
    "regular_parameter":32,
    "wrong_sign_mutant":12,
    "cross_coupling_mutant":12,
    "gradient_zero_mutant":8,
}

def verify():
    rows=[json.loads(line) for line in
          DATA.read_text(encoding="utf-8").splitlines()
          if line.strip()]
    if len(rows)!=96 or len({r["id"] for r in rows})!=96:
        raise AssertionError("DEL-11 requires 96 distinct exact tasks")
    counts=Counter()
    for row in rows:
        kind=row["kind"]
        counts[kind]+=1
        f=FIELDS[row["field"]]
        n=row["n"]
        a,b,c=tuple(row["a"]),tuple(row["b"]),row["c"]
        assert len(a)==len(b)==n
        delta=bad_discriminant(f,a,b,c)
        critical=parameter_is_bad(f,a,b,c)
        _,_,gradient_phase=critical_point(f,a,b,c)
        assert gradient_phase==delta,row["id"]
        assert critical==row["expected_critical"],row["id"]
        if "expected_discriminant_zero" in row:
            assert (delta==0)==row["expected_discriminant_zero"],row["id"]
        if f.q**(2*n)<=512:
            points=brute_force_critical_points(f,a,b,c)
            assert (bool(points)==critical),row["id"]
            assert len(points)==int(critical),row["id"]
        if kind=="critical_exact":
            assert row["label"]=="bad_parameter"
        elif kind=="regular_parameter":
            assert row["label"]=="good_parameter"
        elif kind=="wrong_sign_mutant":
            assert wrong_plus_discriminant(f,a,b,c)==0
            assert delta!=0 and f.p!=2
            assert row["expected_wrong_plus_zero"] is True
            assert row["label"]=="reject_plus_sign"
        elif kind=="cross_coupling_mutant":
            assert cross_coupled_discriminant(f,a,b,c)==0
            assert delta!=0
            assert row["expected_wrong_cross_zero"] is True
            assert row["label"]=="reject_cross_coupling"
        elif kind=="gradient_zero_mutant":
            assert critical and row["label"]=="reject_false_smooth"
        else:
            raise AssertionError(kind)
    assert counts==EXPECTED,counts
    return counts

if __name__=="__main__":
    counts=verify()
    print("DEL-11 exact critical incidence:",sum(counts.values()),"cases")
    print(dict(sorted(counts.items())))

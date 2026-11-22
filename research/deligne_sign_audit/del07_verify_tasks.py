"""DEL-07 deterministic verifier for Katz-to-Poincare Gysin mutants."""
from collections import Counter
from pathlib import Path
from fractions import Fraction as F
import json

from research.deligne_sign_audit.geometry_trace import mat
from research.deligne_sign_audit.del07_oracle import (
    compose_certificate, example, gysin, kernel_action_certificate,
    wrong_forward_dual_certificate,
)

DATA=Path(__file__).with_name("del07_tasks.jsonl")
COUNTS={
    "genuine_boundary":24,
    "noninjective_restriction":8,
    "broken_frobenius_square":8,
    "wrong_dual_action":8,
    "degenerate_perfect_pairing":8,
    "off_by_one_gysin_shift":8,
}

def inspect(row):
    kind=row["kind"]
    if kind=="off_by_one_gysin_shift":
        D,a,j=row["D"],row["ordinaryDegree"],row["rightCompactDegree"]
        source_j=2*D-2-a
        return {
            "right_shift": source_j==j,
            "right_target":source_j+2==row["rightTargetDegree"],
            "wrong_shift":row["wrongCompactDegree"]!=source_j,
        }
    a,b,c=(row[k] for k in ("a","b","c"))
    R,PX,PY,AX,AY=example(
        a=a,b=b,c=c,u=row.get("u",a+b),v=row.get("v",-b),
        p=row.get("p",1),s=row.get("s",2),t=row.get("t",-1))
    if kind=="noninjective_restriction":
        R=mat([[1,0],[0,0],[0,0]])
        AX=mat([[a,0],[0,b]])
        AY=mat([[a,0,0],[0,b,0],[0,0,c]])
    elif kind=="broken_frobenius_square":
        AY=mat([[a,1,a+b],[0,b,-b],[1,0,c]])
    elif kind=="degenerate_perfect_pairing":
        PX=mat([[1,0],[0,0]])
        try: gysin(R,PX,PY)
        except ValueError as exc:
            return {"rejected":True,"reason":str(exc)}
        raise AssertionError("non-perfect PD pairing unexpectedly accepted")
    check=compose_certificate(R,PX,PY,AX,AY,n=row["n"])
    if kind=="genuine_boundary":
        kern=kernel_action_certificate(R,PX,PY,AX,AY,n=row["n"])
        check.update({key:kern[key] for key in (
            "gysin_annihilates_generator","frob_preserves_kernel",
            "kernel_eigenvalue","generator_is_eigenvector",
            "trace_difference_matches")})
    if kind=="wrong_dual_action":
        check["forward_dual_equivariant"]=wrong_forward_dual_certificate(
            R,PX,PY,AX,AY)
    return check

def verify():
    lines=[json.loads(s) for s in DATA.read_text(encoding="utf-8").splitlines()
           if s.strip()]
    assert len(lines)==64 and len({x["id"] for x in lines})==64
    counter=Counter()
    for row in lines:
        kind=row["kind"]
        counter[kind]+=1
        result=inspect(row)
        if kind=="off_by_one_gysin_shift":
            assert row["label"]=="reject_degree"
            assert all(result.values()),row["id"]
            continue
        if kind=="degenerate_perfect_pairing":
            assert row["label"]=="reject_pd"
            assert result["rejected"] and "singular" in result["reason"]
            continue
        for key in ("restriction_injective","gysin_surjective","gysin_equivariant"):
            expected={
                "restriction_injective":"expected_injective",
                "gysin_surjective":"expected_surjective",
                "gysin_equivariant":"expected_equivariant",
            }[key]
            assert result[key]==row[expected],(row["id"],key)
        if kind=="genuine_boundary":
            assert row["label"]=="pass"
            assert result["restriction_equivariant"]
            assert result["frob_preserves_kernel"]
            assert result["generator_is_eigenvector"]
            assert result["gysin_annihilates_generator"]
            assert result["trace_difference_matches"]
            assert result["trace_difference"]==F(row["expected_difference"])
        if kind=="noninjective_restriction":
            assert row["label"]=="reject_surjectivity"
            assert result["restriction_equivariant"]
        if kind=="broken_frobenius_square":
            assert row["label"]=="reject_equivariance"
            assert not result["restriction_equivariant"]
        if kind=="wrong_dual_action":
            assert row["label"]=="reject_dual_action"
            assert result["restriction_equivariant"]
            assert not result["forward_dual_equivariant"]
    assert dict(counter)==COUNTS,(dict(counter),COUNTS)
    return counter

if __name__=="__main__":
    counts=verify()
    print("DEL-07 exact duality cases:",sum(counts.values()))
    print(dict(sorted(counts.items())))

"""Verify all public DEL-02 proof-repair tasks against exact oracles.

Run from repository root:
    python research/deligne_sign_audit/verify_del02_tasks.py
"""
import json
from pathlib import Path

from research.deligne_sign_audit.prime_power_fourier import (
    FIELDS, identity_matrix, one, scalar, shift_poly,
    path_sum_contract, reduced_cyclotomic, verify_path_bound,
)

DATA=Path(__file__).with_name("del02_tasks.jsonl")

def verify():
    tasks=[json.loads(s) for s in DATA.read_text(encoding="utf-8").splitlines() if s]
    assert len(tasks)==51, f"expected 51 tasks, found {len(tasks)}"
    assert len({t["id"] for t in tasks})==len(tasks)
    passes=0
    for task in tasks:
        f=FIELDS[task["field"]]
        q,d,k=f.q,task["d"],task["k"]
        assert q==task["q"]
        space=f.vectors(d)
        h=q-1 if task["h"]=="q-1" else task["h"]
        c=q//2 if task["c"]=="floor(q/2)" else task["c"]
        weight=2 if task["weight"]=="constant_two" else 1
        weights=tuple({x:scalar(weight,f.p) for x in space} for _ in range(k))
        matrix=identity_matrix(d) if task["matrix"]=="identity" else ((0,),)
        matrices=tuple(matrix for _ in range(k-1))
        variant=task["variant"]
        if variant in ("bad-T","zero-h"):
            try:
                verify_path_bound(f,d,weights,matrices,h,c,
                                  t_bound=task.get("T",1))
            except ValueError:
                passes+=1
                continue
            raise AssertionError(f"{task['id']} unexpectedly accepted")
        got=path_sum_contract(f,d,weights,matrices,h,c)
        n=q**d
        predicted=n**(k if variant=="degenerate" else (k+1)//2)
        expected=shift_poly(scalar(predicted,f.p),f.trace(f.mul(h,c)))
        assert reduced_cyclotomic(got)==reduced_cyclotomic(expected),task["id"]
        assert predicted==task["expected_amplitude"]
        cert=verify_path_bound(f,d,weights,matrices,h,c,t_bound=1)
        assert cert["ceiling"]==task["bound_squared"]
        r,s,den=cert["norm_certificate"]
        assert s==0
        assert r==den*task["expected_norm_squared"]
        if variant=="degenerate":
            assert task["label"]=="hypothesis_violation"
            assert not cert["all_forms_nondegenerate"] and not cert["ok"]
        elif variant=="sharp":
            assert task["label"]=="pass"
            assert cert["all_forms_nondegenerate"] and cert["ok"]
            assert task["expected_norm_squared"]==task["bound_squared"]
        elif variant=="even":
            assert task["label"]=="pass"
            assert cert["all_forms_nondegenerate"] and cert["ok"]
            assert task["expected_norm_squared"]<task["bound_squared"]
        else:
            raise AssertionError(f"unsupported variant: {variant}")
        passes+=1
    return passes

if __name__=="__main__":
    print(f"DEL-02 exact proof-repair labels verified: {verify()}/51")

"""Verify all DEL-03 public spectral-pole task labels with exact Fractions."""
import json
from pathlib import Path
from research.deligne_sign_audit.power_sum_poles import (
    spectrum,power_trace,pole_coefficient,certificate,hankel,determinant)

DATA=Path(__file__).with_name("del03_tasks.jsonl")

def verify():
    tasks=[json.loads(s) for s in DATA.read_text(encoding="utf-8").splitlines() if s]
    assert len(tasks)==36
    assert len({t["id"] for t in tasks})==len(tasks)
    counts={}
    for t in tasks:
        kind=t["kind"]
        counts[kind]=counts.get(kind,0)+1
        entries=t["entries"]
        if kind=="genuine":
            cert=certificate(entries)
            assert t["label"]=="valid"
            assert cert["distinct_eigenvalues"]==t["expected_distinct"]
            assert cert["Hankel_det"]==t["expected_det"]
            assert cert["monic_coefficients"]==t["expected_monic_coefficients"]
        elif kind=="virtual_cancel":
            assert t["label"]=="invalid_positive_module"
            assert pole_coefficient(entries,t["hidden"],True)==0
            assert power_trace(entries,2,True)==t["expected_trace2"]
            assert determinant(hankel(entries,2,True))==0
            try: spectrum(entries)
            except ValueError: pass
            else: raise AssertionError(f"{t['id']} accepted virtual multiplicity")
        elif kind=="one_power_only":
            assert t["label"]=="insufficient_powers"
            assert power_trace(entries,1)==t["expected_trace1"]
            assert power_trace(entries,2)==t["expected_trace2"]
        elif kind=="zero_eigenvalue":
            assert t["label"]=="invalid_automorphism"
            try: spectrum(entries)
            except ValueError: pass
            else: raise AssertionError(f"{t['id']} accepted eigenvalue zero")
        else: raise AssertionError(f"unexpected variant: {kind}")
    assert counts=={"genuine":24,"virtual_cancel":6,"one_power_only":3,"zero_eigenvalue":3},counts
    return len(tasks)

if __name__=="__main__":
    print(f"DEL-03 spectral-pole task labels verified: {verify()}/36")

"""DEL-05 verifier for exact rational shadows of variable-extension Lemma 2.

These cases are individually finite arithmetic checks. Assertions about
c_k/k -> 0 are made only for the explicitly specified parametric family
c_k <= sqrt(k), whose convergence is an independent mathematical fact.
No finite oracle certifies the paper's full complex/etale theorem.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import json

CORPUS = Path(__file__).with_name("del05_tasks.jsonl")

def inspect(case, horizon=8):
    q, a, k, e, c = (int(case[z]) for z in ("q", "a", "k", "e", "c"))
    alpha, C, eps = int(case["alpha"]), Fraction(case["C"]), int(case["eps"])
    spectrum = tuple(
        (Fraction(int(row["numerator"]), int(row["denominator"])), int(row["m"]))
        for row in case["spectrum"]
    )
    target = Fraction(alpha) ** (k * e)
    base = Fraction(q) ** (e * (k*a + c))
    traces = [
        sum((m * lam**n for lam,m in spectrum), Fraction(0))
        for n in range(1,horizon+1)
    ]
    remains = [eps*trace for trace in traces]
    bounds = [C * base**n for n in range(1,horizon+1)]
    passes = tuple(abs(R) <= B for R,B in zip(remains,bounds))
    return {
        "passes":passes,
        "target_present":any(lam==target for lam,m in spectrum),
        "positive_multiplicities":all(m>0 for lam,m in spectrum),
        "distinct":len({lam for lam,m in spectrum})==len(spectrum),
        "e_positive":e>0, "k_positive":k>0,
        "sign_unit":eps in (-1,1),
        "sublinear_family_witness":k>0 and 0<=c and c*c<=k,
        "conclusion":Fraction(alpha)<=Fraction(q)**a,
        "traces":tuple(traces),
    }

def verify_corpus():
    rows=[json.loads(line) for line in CORPUS.read_text(encoding="utf-8").splitlines()
          if line.strip()]
    if len(rows)!=62 or len({row["id"] for row in rows})!=len(rows):
        raise AssertionError("invalid DEL-05 task IDs or row count")
    tally=Counter()
    for row in rows:
        result=inspect(row)
        kind=row["kind"]
        tally[kind]+=1
        assert all(key in row for key in
          ("source","evidence_class","expect_trace_bound","expect_target","expect_conclusion"))
        assert result["target_present"]==row["expect_target"], row["id"]
        assert result["conclusion"]==row["expect_conclusion"], row["id"]
        if kind=="one_power_only":
            assert result["passes"][0] and not result["passes"][1],row["id"]
            assert not row["expect_trace_bound"]
        else:
            assert all(result["passes"])==row["expect_trace_bound"],row["id"]
        if kind=="valid":
            assert result["k_positive"] and result["e_positive"]
            assert result["sign_unit"] and result["positive_multiplicities"]
            assert result["distinct"] and result["sublinear_family_witness"]
            assert row["c"]>=0 and row["C"]>0
        elif kind=="linear_loss":
            assert row["c"]==row["k"]
            assert row["c"]/row["k"]==1
            assert result["e_positive"] and result["positive_multiplicities"]
        elif kind=="zero_extension":
            assert row["e"]==0 and not result["e_positive"]
            assert result["positive_multiplicities"]
        elif kind=="one_power_only":
            assert result["e_positive"] and result["positive_multiplicities"]
        elif kind=="virtual_cancellation":
            assert all(x==0 for x in result["traces"])
            assert not result["positive_multiplicities"]
            assert not result["distinct"]
        elif kind=="missing_tensor_eigenvalue":
            assert not result["target_present"]
            assert result["positive_multiplicities"]
        else:
            raise AssertionError("unexpected variant "+kind)
    assert tally=={
        "valid":30, "linear_loss":8, "zero_extension":6,
        "one_power_only":6, "virtual_cancellation":6,
        "missing_tensor_eigenvalue":6},tally
    return tally

if __name__=="__main__":
    tally=verify_corpus()
    print("DEL-05 exact cases verified:", sum(tally.values()))
    print(dict(sorted(tally.items())))

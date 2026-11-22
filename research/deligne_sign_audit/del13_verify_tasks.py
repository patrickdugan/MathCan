"""DEL-13 independent verifier for exact sparse Jacobian ideal receipts."""
from collections import Counter
from pathlib import Path
import json

from research.deligne_sign_audit.prime_power_fourier import FIELDS
from research.deligne_sign_audit.del13_oracle import (
    field_oracle, conic_bezout, wrong_sign_certificate, swapped_factor_certificate,
    poly_add, poly_mul, constant,
)

DATA=Path(__file__).with_name("del13_tasks.jsonl")
COUNTS={
    "off_discriminant_unit":36,
    "on_discriminant_obstruction":36,
    "wrong_sign":12,
    "wrong_factor":12,
}

def verify():
    rows=[json.loads(line) for line in DATA.read_text(encoding="utf-8").splitlines()
          if line.strip()]
    assert len(rows)==96 and len({r["id"] for r in rows})==96
    counts=Counter()
    for row in rows:
        name,a,b,c=(row[x] for x in ("field","a","b","c"))
        kind=row["kind"]
        counts[kind]+=1
        f=FIELDS[name]
        receipt=field_oracle(name,a,b,c)
        assert receipt["identity"],row["id"]
        d=receipt["delta"]
        assert (d!=0)==row["expected_delta_nonzero"],row["id"]
        if kind=="off_discriminant_unit":
            assert row["label"]=="unit_ideal" and row["expected_unit"]
            cert=receipt["unit_certificate"]
            assert cert is not None and cert["unit_identity"]
            assert receipt["unit_if_nonzero"]
            assert not receipt["singular_if_zero"]
            polynomials=conic_bezout(f,a,b,c)
            lhs=poly_add(f,
                poly_mul(f,cert["coeffs"]["F"],polynomials["F"]),
                poly_mul(f,cert["coeffs"]["dx"],polynomials["dx"]))
            assert lhs==constant(f,1),row["id"]
        elif kind=="on_discriminant_obstruction":
            assert row["label"]=="proper_ideal_witness"
            assert not row["expected_unit"] and row["expected_singular"]
            assert not receipt["unit_if_nonzero"]
            assert receipt["singular_if_zero"]
            assert receipt["singular_obstruction"]["generator_evaluations"]==(0,0,0)
        elif kind=="wrong_sign":
            assert row["label"]=="reject_sign"
            assert wrong_sign_certificate(f,a,b,c)==0
            assert d!=0 and row["expected_wrong_sign_zero"]
        elif kind=="wrong_factor":
            assert row["label"]=="reject_derivative_factor"
            assert not swapped_factor_certificate(f,a,b,c)
            assert not row["expected_wrong_factor_identity"]
        else:
            raise AssertionError(kind)
    assert counts==COUNTS,counts
    return counts

if __name__=="__main__":
    counts=verify()
    print("DEL-13 exact polynomial Jacobian receipts:",sum(counts.values()))
    print(dict(sorted(counts.items())))

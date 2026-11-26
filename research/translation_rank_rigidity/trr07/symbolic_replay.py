#!/usr/bin/env python3
"""Rebuild each new chart using FLINT, then replay its integer certificate.

The search uses PARI. This replay derives the generic recurrence with FLINT,
checks chart-factor coverage, and runs the adapted exact BigInt checker, which
rebuilds the residue ratios directly from H and lambda. Neither g_i nor their
norms from the search are trusted inputs.
"""
import argparse
import json
import subprocess
from pathlib import Path
from symbolic_generic import CTX, R, T, coordinates, derive


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("certificate",type=Path)
    parser.add_argument("--expected-order",type=int)
    args=parser.parse_args()
    certificates=json.loads(args.certificate.read_text())
    assert isinstance(certificates,dict) and certificates, "nonempty certificate dictionary required"
    if args.expected_order is not None:
        assert set(certificates)=={str(args.expected_order)}, "certificate order differs from requested job"
    for key, cert in certificates.items():
        n=int(key)
        assert n>=7 and all(n%d for d in range(2,int(n**0.5)+1))
        rebuilt=derive(n)
        assert len(rebuilt["candidate_factors"])==1
        terms=rebuilt["candidate_factors"][0]["coefficients"]
        f=CTX.from_dict({tuple(e):int(c) for e,c in terms})
        claimed=CTX.constant(0)
        for i, row in enumerate(cert["f"]):
            for j, c in enumerate(row):
                claimed += int(c)*R**i*T**j
        assert claimed==f, "stored chart differs from generic recurrence"
        assert f.degrees()[0]==cert["rank"]
        assert rebuilt["candidate_factors"][0]["multiplicity"]==1
        assert rebuilt["unit"] in ("1","-1"), "extra exceptional characteristic in order equation"
        # Removed factors are units for smooth exact order N>=7, by the
        # standard Tate normalization and x(5T)=rt(t-1). Every remaining
        # denominator is retained in the original recurrence and checked
        # invertible in the quotient by the Node replay.
        assert all(factor["polynomial"] in ("r","r - 1","t","t - 1")
                   for factor in rebuilt["removed_obvious_units"])
        print(f"[ok] independent generic order-{n} chart and unit factors",flush=True)
    verifier=Path(__file__).with_name("symbolic_verify.mjs")
    subprocess.run(["node",str(verifier),str(args.certificate)],check=True)


if __name__=="__main__":
    main()

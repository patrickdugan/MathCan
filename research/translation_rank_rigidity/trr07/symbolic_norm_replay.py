#!/usr/bin/env python3
"""Independent FLINT elimination/fibre replay of a stored certificate.

This checks the complete zero-locus exclusion for the stored g_i. The bridge
from H*lambda to those g_i is deliberately not asserted here; that requires
symbolic_replay.py or a separately checked geometric proof.
"""
import argparse
import hashlib
import json
from math import isqrt
import time
from pathlib import Path
from flint import fmpz_poly, fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx
from symbolic_generic import CTX, R, T, derive


def bivariate(rows):
    return CTX.from_dict({(i,j):int(c) for i,row in enumerate(rows) for j,c in enumerate(row) if int(c)})


def replay(certificate):
    start=time.monotonic()
    results=[]
    data=json.loads(certificate.read_text())
    assert isinstance(data,dict) and data
    for key, cert in data.items():
        n=int(key)
        model=derive(n)
        assert len(model["candidate_factors"])==1
        f=bivariate(cert["f"])
        assert f==CTX.from_dict({tuple(e):int(c) for e,c in model["candidate_factors"][0]["coefficients"]})
        assert model["unit"] in ("1","-1")
        assert all(z["polynomial"] in ("r","r - 1","t","t - 1") for z in model["removed_obvious_units"])
        equations=list(map(str,range(2,(n+1)//2)))
        assert set(cert["g"])==set(cert["P"])==set(cert["W"])==set(cert["norm_exp"])==set(equations)
        polynomials=[]
        for i in equations:
            g=bivariate(cert["g"][i]["num"])
            norm=f.resultant(g,0)
            a,b=cert["norm_exp"][i]
            assert isinstance(a,int) and a>=0 and isinstance(b,int) and b>=0
            residual=fmpz_poly([int(c) for c in cert["P"][i]])
            asserted=CTX.constant(0)
            for j,c in enumerate(residual):
                asserted += int(c)*T**j
            assert norm==T**a*(T-1)**b*asserted, f"norm mismatch at {n}:{i}"
            polynomials.append(residual)
        identity=sum((fmpz_poly([int(c) for c in cert["W"][i]])*p for i,p in zip(equations,polynomials)),fmpz_poly())
        integer=int(cert["n0"])
        assert integer>0 and identity==fmpz_poly([integer])
        remaining=integer
        fibres=[]
        for keyp,entry in cert["primes"].items():
            p=int(keyp)
            assert p>=2 and all(p%d for d in range(2,isqrt(p)+1))
            assert remaining%p==0
            while remaining%p==0:
                remaining//=p
            P=fmpz_mod_poly_ctx(p)
            gcd=P([])
            for value in polynomials:
                gcd=gcd.gcd(P(value))
            gcd=gcd.monic()
            product=P([1])
            for factor in entry["factors"]:
                phi=P([int(c) for c in factor["phi"]])
                assert phi.is_monic() and phi.is_irreducible()
                assert isinstance(factor["mult"],int) and factor["mult"]>0
                product*=phi**factor["mult"]
            assert product==gcd
            for factor in entry["factors"]:
                phi=P([int(c) for c in factor["phi"]])
                K=fq_default_ctx(modulus=phi,fq_type="FQ_NMOD")
                Q=fq_default_poly_ctx(K)
                tau=K.gen()
                def evaluate(rows):
                    coefficients=[]
                    for row in rows:
                        value=K(0)
                        for c in reversed(row):
                            value=value*tau+K(int(c))
                        coefficients.append(value)
                    return Q(coefficients)
                gamma=evaluate(cert["f"])
                for i in equations:
                    gamma=gamma.gcd(evaluate(cert["g"][i]["num"]))
                gamma=gamma.monic()
                claimed=Q([K([int(c) for c in row]) for row in factor["Gamma"]])
                assert gamma==claimed
                r=Q([K(0),K(1)])
                b=r*tau*(r-1)
                c=tau*(r-1)
                a1=1-c
                b2=a1*a1-4*b;b4=-a1*b;b6=b*b;b8=-b*b*b
                delta=-b2*b2*b8-8*b4*b4*b4-27*b6*b6+9*b2*b4*b6
                power=max(1,gamma.degree())
                assert power==factor["discriminant_power"]
                assert (delta**power)%gamma==Q([])
                fibres.append({"p":p,"residue_degree":phi.degree(),"fibre_degree":gamma.degree(),"all_roots_singular":True})
        assert remaining==1
        results.append({"order":n,"norms_recomputed":len(polynomials),"integer":str(integer),"fibres":fibres})
    return {"schema":"trr07-independent-elimination-replay-v1","status":"passed",
            "elapsed_seconds":time.monotonic()-start,"orders":results,
            "scope":"stored compressed equations, integral elimination, and every exceptional fibre",
            "remaining_proof_obligation":"reconstruct stored g_i from H*lambda in the localized integral algebra",
            "certificate_sha256":hashlib.sha256(certificate.read_bytes()).hexdigest()}


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("certificate",type=Path)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    result=replay(args.certificate)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

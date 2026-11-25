#!/usr/bin/env python3
"""Checkpointed exact search for new interpolation certificates.

Requires cypari2 and python-flint. A parent process enforces a wall-clock
budget. Timeout receipts preserve the last completed stage and never assert
exclusion. A successful search writes polynomial identities and a complete
finite-characteristic fibre analysis, for separate replay.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path
sys.set_int_max_str_digits(0)

HERE = Path(__file__).resolve().parent


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def worker(args):
    import cypari2
    from symbolic_generic import derive

    start = time.monotonic()
    order = args.order
    out = args.output
    out.mkdir(parents=True, exist_ok=True)
    receipt_path = out / f"receipt{order}.json"
    receipt = {"schema": "trr07-symbolic-search-v1", "order": order,
               "status": "running", "stages": [],
               "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "proof_obligations": ["independent certificate replay", "chart coverage in every characteristic"]}

    def checkpoint(stage, **details):
        receipt["stages"].append(dict(stage=stage, elapsed_seconds=time.monotonic() - start, **details))
        receipt["last_stage"] = stage
        atomic_json(receipt_path, receipt)
        print(json.dumps(receipt["stages"][-1]), flush=True)

    checkpoint("initialization")
    model = derive(order)
    atomic_json(out / f"generic{order}.json", model)
    assert len(model["candidate_factors"]) == 1
    candidate = model["candidate_factors"][0]
    assert candidate["multiplicity"] == 1
    f_text = candidate["polynomial"]
    checkpoint("generic_chart_factorization", degree_r=candidate["degrees"][0], degree_t=candidate["degrees"][1])

    pari = cypari2.Pari()
    pari.allocatemem(args.memory_mb * 1024 * 1024, silent=True)
    pari("r; t;")
    pari(f"N={order}; n=(N-1)/2; f={f_text}; d=poldegree(f,r);")
    assert int(pari("pollead(f,r)")) == 1
    n, d = int(pari("n")), int(pari("d"))

    def zp(expr):
        values = [str(x) for x in pari(f"Vecrev({expr})")]
        while values and values[-1] == "0":
            values.pop()
        return values

    def relt(expr):
        return [zp(f"polcoeff({expr},{i},r)") for i in range(d)]

    pari("strip(q)=my(e0=0,e1=0);if(q==0,error(\"zero norm\"));while(subst(q,t,0)==0,q=q/t;e0++);while(subst(q,t,1)==0,q=q/(t-1);e1++);[q,e0,e1]")
    pari("b=r*t*(r-1);c=t*(r-1);a1=1-c;a3=-b;a2=-b;")
    pari("X=vector(n+1);Y=vector(n+1);slopes=vector(n);slopes[1]=Mod(a1/2,f);X[1]=Mod(0,f);Y[1]=Mod(0,f);X[2]=Mod(b,f);Y[2]=Mod(b*c,f);")
    for i in range(2, n + 1):
        pari(f"m=Y[{i}]/X[{i}];slopes[{i}]=m+a1/2;X[{i+1}]=m^2+a1*m+b-X[{i}];Y[{i+1}]=b-(m+a1)*X[{i+1}];")
    assert pari("X[n]==X[n+1]")
    checkpoint("quotient_coordinates", rank=d, order_equation_verified=True)

    # The written TRR-06 residue theorem gives 2(u_i-u_1)=a_i^2-a_1^2-N(x_i-x_1).
    # Independent replay additionally reconstructs H and lambda directly.
    pari("b2=a1^2+4*a2;b4=a1*a3;b6=a3^2;b8=a2*a3^2;")
    pari("disc=-b2^2*b8-8*b4^3-27*b6^2+9*b2*b4*b6;")
    pari("xp=vector(n,i,2*Y[i]+a1*X[i]+a3);xpp=vector(n,i,6*X[i]^2+b2*X[i]+b4);")
    pari("e1=vector(n);G=vector(n-1);g=vector(n-1);dG=vector(n-1);sd=vector(n-1);")
    if args.residue_method == "direct":
        for i in range(1, n + 1):
            pari(f"e1[{i}]=-xp[{i}]*sum(j=1,n,if(j=={i},0,1/(X[{i}]-X[j])))-xpp[{i}]/(2*xp[{i}]);")
            checkpoint("residue_coefficient", index=i, method="direct")
    else:
        # Logarithmic translation cocycle: a_(i+1)=a_i+a_1+N*s_i.
        # Oddness a_(n+1)=-a_n determines a_1 over Q; the independently
        # replayed integer identities justify all later specializations.
        pari("e1[1]=-2*sum(i=1,n-1,slopes[i])-slopes[n];for(i=1,n-1,e1[i+1]=e1[i]+e1[1]+N*slopes[i]);")
        checkpoint("residue_coefficients", method="translation_cocycle_recurrence")
    for i in range(1, n):
        pari(f"G[{i}]=(e1[{i+1}]^2-e1[1]^2-N*(X[{i+1}]-X[1]))/2;dG[{i}]=denominator(content(lift(G[{i}])));g[{i}]=lift(G[{i}])*dG[{i}];sd[{i}]=strip(dG[{i}]);")
        assert pari(f"sd[{i}][1]==1"), "unaccounted denominator"
    certificate = {"N": order, "n": n, "rank": d,
                   "f": [zp(f"polcoeff(f,{i},r)") for i in range(d+1)],
                   "generic_factorization": model,
                   "g": {str(i+1): {"num": relt(f"g[{i}]"),
                                     "den_exp_t": int(pari(f"sd[{i}][2]")),
                                     "den_exp_t1": int(pari(f"sd[{i}][3]"))}
                         for i in range(1,n)},
                   "P": {}, "norm_exp": {}, "W": {}, "primes": {}}
    atomic_json(out / f"partial{order}.json", certificate)
    checkpoint("compressed_ratios", degree_pairs=[[int(pari(f"poldegree(g[{i}],r)")), int(pari(f"poldegree(g[{i}],t)"))] for i in range(1,n)])

    pari("Nm=vector(n-1);S=vector(n-1);P=vector(n-1);")
    for i in range(1,n):
        pari(f"Nm[{i}]=polresultant(f,g[{i}],r);S[{i}]=strip(Nm[{i}]);P[{i}]=S[{i}][1];")
        certificate["P"][str(i+1)] = zp(f"P[{i}]")
        certificate["norm_exp"][str(i+1)] = [int(pari(f"S[{i}][2]")), int(pari(f"S[{i}][3]"))]
        atomic_json(out / f"partial{order}.json", certificate)
        checkpoint("norm", index=i+1, residual_degree=int(pari(f"poldegree(P[{i}])")),
                   max_coefficient_bits=max(abs(int(c)).bit_length() for c in certificate["P"][str(i+1)]))

    from symbolic_lattice import bezout
    integer,cofactors,K,lattice_shape=bezout(list(certificate["P"].values()),args.cofactor_degree)
    pari(f"n0={integer};W="+str(cofactors)+";")
    pari("W=vector(n-1,i,Polrev(W[i],t));")
    assert pari("sum(i=1,n-1,W[i]*P[i])==n0")
    certificate["W"] = {str(i+1): zp(f"W[{i}]") for i in range(1,n)}
    certificate["n0"] = str(pari("n0"))
    certificate["n0_factorisation"] = str(pari("factor(n0)"))
    atomic_json(out / f"partial{order}.json", certificate)
    checkpoint("integer_bezout", integer=certificate["n0"], factorization=certificate["n0_factorisation"], cofactor_degree=K,
               lattice_algorithm="FLINT_HNF_LLL", lattice=lattice_shape)

    for ai in range(1,int(pari("matsize(factor(n0))[1]"))+1):
        p = int(pari(f"factor(n0)[{ai},1]"))
        pari(f"p={p};Dp=0;for(i=1,n-1,Dp=gcd(Dp,P[i]*Mod(1,p)));Dp=lift(Dp/pollead(Dp));FD=factor(Dp*Mod(1,p));")
        pent = {"gcd_P": zp("Dp"), "factors": []}
        for bi in range(1,int(pari("matsize(FD)[1]"))+1):
            pari(f"phi=lift(FD[{bi},1]);dphi=poldegree(phi);")
            linear = int(pari("dphi")) == 1
            pari("t0=Mod(-polcoeff(phi,0),p);" if linear else "t0=ffgen(phi*Mod(1,p),'a);")
            pari("Gam=subst(f,t,t0)*t0^0;for(i=1,n-1,Gam=gcd(Gam,subst(g[i],t,t0)*t0^0));Gam=Gam/pollead(Gam);")
            # Gamma can retain nilpotent multiplicities. Raising Delta to
            # deg(Gamma) covers every such multiplicity while testing its
            # geometric zero set, including higher-degree residue extensions.
            pari("disc_power=max(1,poldegree(Gam));remainder_disc=(subst(disc,t,t0)*t0^0)^disc_power%Gam;")
            singular = bool(pari("remainder_disc==0"))
            gamma = []
            for ri in range(int(pari("poldegree(Gam)"))+1):
                expr=f"(polcoeff(Gam,{ri})*t0^0)"
                gamma.append([str(pari(f"lift({expr})"))] if linear else [str(c) for c in pari(f"lift(Vecrev(({expr}).pol))")])
            pent["factors"].append({"phi": zp("phi"), "mult":int(pari(f"FD[{bi},2]")),
                                     "Gamma": gamma, "deg_Gamma":len(gamma)-1,
                                     "discriminant_power":int(pari("disc_power")),
                                     "discriminant_remainder_zero":singular})
            checkpoint("exceptional_fibre", characteristic=p, residue_degree=int(pari("dphi")),
                       fibre_degree=len(gamma)-1, all_roots_singular=singular)
        certificate["primes"][str(p)] = pent
        atomic_json(out / f"partial{order}.json", certificate)

    all_singular = all(fac["discriminant_remainder_zero"] for pc in certificate["primes"].values() for fac in pc["factors"])
    certificate["search_status"] = "exclusion_candidate" if all_singular else "fibre_requires_resolution"
    atomic_json(out / f"certificate{order}.json", {str(order): certificate})
    receipt["status"] = certificate["search_status"]
    checkpoint("search_finished", all_exceptional_fibres_singular=all_singular)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--order",type=int,required=True)
    parser.add_argument("--output",type=Path,default=HERE/"symbolic_results")
    parser.add_argument("--seconds",type=int,default=900)
    parser.add_argument("--memory-mb",type=int,default=768)
    parser.add_argument("--cofactor-degree",type=int)
    parser.add_argument("--residue-method",choices=["direct","recurrence"],default="recurrence")
    parser.add_argument("--worker",action="store_true")
    args=parser.parse_args()
    if args.worker:
        worker(args)
        return
    args.output.mkdir(parents=True,exist_ok=True)
    cmd=[sys.executable,str(Path(__file__).resolve()),"--worker","--order",str(args.order),
         "--output",str(args.output.resolve()),"--memory-mb",str(args.memory_mb),
         "--residue-method",args.residue_method]
    if args.cofactor_degree is not None:
        cmd += ["--cofactor-degree",str(args.cofactor_degree)]
    logfile=args.output/f"search{args.order}.log"
    with logfile.open("w") as log:
        try:
            completed=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=args.seconds)
            status=None if completed.returncode==0 else "error"
        except subprocess.TimeoutExpired:
            status="timeout"
    receipt_path=args.output/f"receipt{args.order}.json"
    receipt=json.loads(receipt_path.read_text()) if receipt_path.exists() else {"order":args.order}
    receipt["wall_budget_seconds"]=args.seconds
    if status:
        receipt["status"]=status
        receipt["exclusion_proved"]=False
    atomic_json(receipt_path,receipt)
    print(json.dumps(receipt))
    if status=="error":
        print(logfile.read_text()[-5000:])
        raise SystemExit(1)


if __name__=="__main__":
    main()

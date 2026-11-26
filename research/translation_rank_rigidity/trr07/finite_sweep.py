#!/usr/bin/env python3
"""Reproducible exact interpolation sweeps over prime and extension fields.

Examples:
  python finite_sweep.py --prime-max 101 --output finite_prime.json
  python finite_sweep.py --field 7:2 --field 5:3 --models 16 --output finite_extensions.json
  python finite_sweep.py --field 7:5 --models 8 --max-order 127 --output finite_large.json

Prime fields enumerate every nonsingular short model unless --models is set.
Extension fields use a fixed-seed cohort. Every rational subgroup in the chosen
prime-order range is tested on each curve, including rank-two torsion cases.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import time

from finite_fields import Field, Curve, prime, prime_factors, residue_profile, direct_matrix_check


def signed_frobenius_size(q,n):
    if q % n == 0:return 0
    seen=set(); v=1
    while v not in seen:
        seen.add(v);seen.add((-v)%n);v=v*q % n
    return len(seen)


def field_checks(F):
    """Independent long-polynomial checks plus sampled field axioms."""
    rng=random.Random(0xA17+F.q); checks=0
    for _ in range(512):
        a,b,c=[rng.randrange(F.q) for _ in range(3)]
        assert F.mul(a,F.add(b,c))==F.add(F.mul(a,b),F.mul(a,c))
        assert F.add(a,F.neg(a))==0
        assert F.pow(a,F.q)==a
        if a:assert F.mul(a,F.inv(a))==1
        if F.degree>1:
            assert F.mul(a,b)==F.polynomial_mul(a,b)
        checks+=1
    return checks


def tate5_controls(F):
    """Known smooth exceptions, explicitly including parameters outside F_p."""
    if F.p==5:return []
    out=[]
    for t in range(F.q):
        if F.sub(F.sub(F.mul(t,t),t),1):continue
        a1=F.sub(1,t);a2=F.neg(t);a3=F.neg(t)
        b2=F.add(F.mul(a1,a1),F.mul(F.const(4),a2))
        b4=F.mul(a1,a3);b6=F.mul(a3,a3)
        a=F.sub(F.div(b4,F.const(2)),F.div(F.mul(b2,b2),F.const(48)))
        b=F.add(F.sub(F.div(F.pow(b2,3),F.const(864)),F.div(F.mul(b2,b4),F.const(24))),F.div(b6,F.const(4)))
        P=(F.div(b2,F.const(12)),F.div(a3,F.const(2)))
        C=Curve(F,a,b);seq=C.sequence(P,5)
        u,rat,lam=residue_profile(C,seq,complete=True)
        assert u is not None and direct_matrix_check(C,seq)==u
        expected=F.add(F.mul(t,t),F.div(b2,F.const(12)))
        assert u==expected
        out.append(dict(parameter=t,parameter_outside_prime_field=t>=F.p,
                        a=a,b=b,point=P,assigned_value=u,ratios=rat,
                        discriminant=C.discriminant,curve_order=C.order,
                        subgroup=seq,annihilator=lam,
                        direct_matrix_verified=True))
    return out


def model_cohort(F,models,seed):
    if models==0:
        for a in range(F.q):
            for b in range(F.q):yield a,b
        return
    rng=random.Random(seed+F.q); seen=set(); fixed=[(0,1),(0,F.const(2)),(1,0),(F.const(2),0)]
    for a,b in fixed:
        if (a,b) not in seen and len(seen)<models:
            seen.add((a,b));yield a,b
    while len(seen)<models:
        a,b=rng.randrange(F.q),rng.randrange(F.q)
        if (a,b) not in seen:
            seen.add((a,b));yield a,b


def run_field(p,degree,models,max_order,matrix_max,seed,case_file,max_seconds=0):
    started=time.monotonic();F=Field(p,degree); arithmetic_checks=field_checks(F)
    counts=Counter(); strata=Counter(); orders=Counter(); omissions=Counter(); iso=set(); exception_iso=set()
    exceptions=[]; tested_strata={}; controls=tate5_controls(F); generator_checks=0; timeouts=[]
    for a,b in model_cohort(F,models,seed):
        if max_seconds and time.monotonic()-started>max_seconds:
            timeouts.append(dict(stage='between_models',limit_seconds=max_seconds,next_a=a,next_b=b))
            break
        counts['coefficient_pairs_visited']+=1
        try:C=Curve(F,a,b)
        except AssertionError as exc:
            if str(exc)!="singular short equation":raise
            counts['singular_models_skipped']+=1;continue
        counts['smooth_models']+=1
        isokey=F.isomorphism_key(a,b); iso.add(isokey)
        ordinary='supersingular' if C.trace%p==0 else 'ordinary'
        special='j0' if C.j==0 else 'j1728' if C.j==F.const(1728) else 'generic_j'
        counts['curve_'+ordinary]+=1;counts['curve_'+special]+=1
        for n in prime_factors(C.order):
            if n<5:continue
            if max_order and n>max_order:
                omissions[str(n)]+=1;continue
            subgroup_seen=set()
            for seq in C.subgroups(n):
                key=tuple(sorted(seq[1:]));assert key not in subgroup_seen;subgroup_seen.add(key)
                counts['subgroup_instances']+=1;orders[str(n)]+=1
                orbit=signed_frobenius_size(F.q,n)
                splitting='matching_characteristic' if n==p else 'tame_transitive' if orbit==n-1 else 'tame_nontransitive'
                full='full_prime_group' if n==C.order else 'proper_subgroup'
                stratum='|'.join([splitting,special,ordinary,full]);strata[stratum]+=1
                for tag in [splitting,special,ordinary,full]:counts['subgroups_'+tag]+=1
                u,rat,lam=residue_profile(C,seq)
                direct=(n<=matrix_max or u is not None)
                if direct:
                    assert direct_matrix_check(C,seq)==u
                    counts['direct_matrix_checks']+=1
                # Every subgroup is checked with a second generator. The point set,
                # intrinsic residue weights, and existence answer must be unchanged.
                seq2=[seq[(2*i)%n] for i in range(n)]
                u2,rat2,lam2=residue_profile(C,seq2)
                assert u2==u and all(lam2[i]==lam[(2*i)%n] for i in range(n))
                generator_checks+=1
                if stratum not in tested_strata:
                    tested_strata[stratum]=dict(a=a,b=b,order=C.order,n=n,generator=seq[1])
                record=dict(p=p,degree=degree,q=F.q,a=a,b=b,curve_order=C.order,
                            trace=C.trace,subgroup_order=n,generator=seq[1],
                            signed_frobenius_orbit_size=orbit,stratum=stratum,
                            lower_degree_exists=u is not None,pole_value=u,
                            first_ratios=rat,direct_matrix_verified=direct)
                if case_file:case_file.write(json.dumps(record,separators=(',',':'))+'\n')
                if u is not None:
                    counts['exceptions']+=1;exception_iso.add(isokey)
                    record.update(subgroup=seq,annihilator=lam,discriminant=C.discriminant,j=C.j)
                    exceptions.append(record)
                    if n!=5:counts['new_smooth_exception']+=1
    counts['field_isomorphism_classes']=len(iso)
    counts['exception_curve_isomorphism_classes']=len(exception_iso)
    counts['generator_invariance_checks']=generator_checks
    counts['field_arithmetic_checks']=arithmetic_checks
    counts['order5_positive_controls']=len(controls)
    counts['order5_controls_outside_prime_field']=sum(v['parameter_outside_prime_field'] for v in controls)
    return dict(field=F.metadata(),sampling=dict(mode='all_short_models' if models==0 else 'fixed_seed_cohort',
                  seed=seed,coefficient_pairs_requested=models or F.q**2,
                  max_subgroup_order=max_order or 'all',matrix_check_through_order=matrix_max,
                  isomorphism_scope='F_q-isomorphism classes of tested short equations; subgroup instances are per equation'),
                counts=dict(counts),by_subgroup_order=dict(orders),by_stratum=dict(strata),
                omitted_curve_prime_factors=dict(omissions),stratum_examples=tested_strata,
                exceptions=exceptions,order5_controls=controls,
                failures=[],timeouts=timeouts,complete=not timeouts,
                elapsed_seconds=round(time.monotonic()-started,6))


def main():
    ap=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--field',action='append',default=[],help='prime:extension_degree, repeatable')
    ap.add_argument('--p',type=int,help='one field, with --degree')
    ap.add_argument('--degree',type=int,default=1)
    ap.add_argument('--prime-max',type=int,default=0)
    ap.add_argument('--models',type=int,default=None,help='0 enumerates prime models; extension default 16')
    ap.add_argument('--max-order',type=int,default=127,help='0 tests all prime divisors')
    ap.add_argument('--matrix-max','--direct-max-order',dest='matrix_max',type=int,default=13)
    ap.add_argument('--seed',type=int,default=20261125)
    ap.add_argument('--max-seconds-per-field',type=float,default=600,
                    help='records an incomplete field and exits nonzero when the budget expires')
    ap.add_argument('--output',type=Path,default=Path('finite_sweep.json'))
    ap.add_argument('--cases',type=Path,help='optional complete per-subgroup JSONL ledger')
    args=ap.parse_args()
    fields=[tuple(map(int,s.split(':'))) for s in args.field]
    if args.p:fields.append((args.p,args.degree))
    fields += [(p,1) for p in range(5,args.prime_max+1) if prime(p)]
    fields=list(dict.fromkeys(fields));assert fields,'pass --field or --prime-max'
    args.output.parent.mkdir(parents=True,exist_ok=True)
    handle=None
    if args.cases:
        args.cases.parent.mkdir(parents=True,exist_ok=True);handle=args.cases.open('w')
    result=dict(schema='trr07-finite-sweep-v1',python=platform.python_version(),
                source_sha256={p.name:sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(__file__).with_name('finite_fields.py')]},
                fields=[],counts={},errors=[],scope='exact finite calculations; sampled fields do not establish an algebraic-closure exclusion')
    total=Counter();failed=False
    for p,d in fields:
        models=args.models if args.models is not None else (0 if d==1 else 16)
        try:
            row=run_field(p,d,models,args.max_order,args.matrix_max,args.seed,handle,args.max_seconds_per_field)
            result['fields'].append(row);total.update(row['counts'])
            if not row['complete']:failed=True
            print(json.dumps(dict(q=p**d,counts=row['counts'],elapsed_seconds=row['elapsed_seconds']),sort_keys=True),flush=True)
        except Exception as exc:
            result['errors'].append(dict(p=p,degree=d,error=repr(exc)));failed=True
            print(json.dumps(result['errors'][-1]),flush=True)
        result['counts']=dict(total)
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
        if handle:handle.flush()
    if handle:handle.close()
    if failed:raise SystemExit(1)
    if total['new_smooth_exception']:raise SystemExit(2)


if __name__=='__main__':main()

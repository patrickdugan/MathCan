#!/usr/bin/env python3
"""Independent exact residue reconstruction with cleared denominators.

This checker uses the residue identity proved in uniform_probe.md. Its arithmetic
reconstructs local Laurent coefficients from the kernel polynomial, independently
of the PARI search and independently of the logarithmic-cocycle shortcut.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
from math import isqrt
import flint
from symbolic_generic import coordinates, derive

CTX=flint.fmpz_mpoly_ctx.get(['r','t'],'lex')
r,t=CTX.gens()


def from_rows(rows):
    return CTX.from_dict({(i,j):int(c) for i,row in enumerate(rows) for j,c in enumerate(row) if int(c)})


def from_generic(poly):
    assert all(v.denominator==1 for v in poly.coeffs())
    return CTX.from_dict({k:int(v) for k,v in poly.to_dict().items()})


def fraction_class(f):
    class Fraction:
        normalizations=0
        def __init__(self,num=0,den=1):
            if isinstance(num,Fraction):
                self.num,self.den=num.num,num.den;return
            num=CTX.constant(num) if isinstance(num,int) else num
            den=CTX.constant(den) if isinstance(den,int) else den
            self.num=num;self.den=den
            assert self.den,'zero generic denominator'
            if not self.num:self.den=CTX.constant(1);return
            common=self.num.gcd(self.den)
            self.num//=common;self.den//=common
            if self.den.leading_coefficient()<0:self.num=-self.num;self.den=-self.den
            Fraction.normalizations+=1
        def __add__(self,other):
            other=Fraction(other)
            if self.den==other.den:return Fraction(self.num+other.num,self.den)
            common=self.den.gcd(other.den)
            left=self.den//common;right=other.den//common
            return Fraction(self.num*right+other.num*left,self.den*right)
        __radd__=__add__
        def __neg__(self):return Fraction(-self.num,self.den)
        def __sub__(self,other):return self+-Fraction(other)
        def __rsub__(self,other):return Fraction(other)+-self
        def __mul__(self,other):
            other=Fraction(other)
            a=self.num.gcd(other.den);b=other.num.gcd(self.den)
            return Fraction((self.num//a)*(other.num//b),(self.den//b)*(other.den//a))
        __rmul__=__mul__
        def __truediv__(self,other):
            other=Fraction(other)
            assert other.num,'division by zero generic fraction'
            return self*Fraction(other.den,other.num)
        def __pow__(self,e):
            assert e>=0
            return Fraction(self.num**e,self.den**e)
        def equal(self,other):
            other=Fraction(other)
            return not ((self.num*other.den-other.num*self.den)%f)
    return Fraction


def verify(certificate_path,output,expected_order=None):
    started=time.monotonic();data=json.loads(certificate_path.read_text())
    assert len(data)==1
    key,cert=next(iter(data.items()));N=int(key);n=(N-1)//2
    assert N>=7 and all(N%d for d in range(2,isqrt(N)+1)), 'prime order at least seven required'
    if expected_order is not None:assert N==expected_order,'certificate order differs from requested job'
    assert cert['N']==N and cert['n']==n
    assert set(cert['g'])=={str(i) for i in range(2,n+1)},'complete residue equation set required'
    for entry in cert['g'].values():
        assert type(entry['den_exp_t']) is int and entry['den_exp_t']>=0
        assert type(entry['den_exp_t1']) is int and entry['den_exp_t1']>=0
    receipt=dict(schema='trr07-flint-certificate-replay-v1',order=N,status='running',
                 certificate_sha256=hashlib.sha256(certificate_path.read_bytes()).hexdigest(),
                 stages=[],method='Direct kernel-polynomial Laurent coefficients in free Z[r,t], final integer remainders modulo f, followed by independent elimination and all exceptional fibres; uses the proved residue identity and no PARI arithmetic')
    output.parent.mkdir(parents=True,exist_ok=True)
    def checkpoint(stage,**kwargs):
        row=dict(stage=stage,elapsed_seconds=round(time.monotonic()-started,6),**kwargs)
        receipt['stages'].append(row);output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(row),flush=True)
    f=from_rows(cert['f']);assert f.degrees()[0]==cert['rank']
    generic=derive(N);assert len(generic['candidate_factors'])==1
    claimed=CTX.from_dict({tuple(e):int(c) for e,c in generic['candidate_factors'][0]['coefficients']})
    assert claimed==f and generic['candidate_factors'][0]['multiplicity']==1
    assert generic['unit'] in ('1','-1')
    assert all(row['polynomial'] in ('r','r - 1','t','t - 1') for row in generic['removed_obvious_units'])
    checkpoint('generic_order_chart',rank=cert['rank'])
    Q=fraction_class(f);xs,ys=coordinates(n+1)
    X=[Q(from_generic(z.num),from_generic(z.den)) for z in xs]
    Y=[Q(from_generic(z.num),from_generic(z.den)) for z in ys]
    assert X[n].equal(X[n+1])
    b=Q(r*t*(r-1));c=Q(t*(r-1));a1=1-c;b2=a1*a1-4*b;b4=-a1*b
    xp=[Q(0)]+[2*Y[i]+a1*X[i]-b for i in range(1,n+1)]
    xpp=[Q(0)]+[6*X[i]*X[i]+b2*X[i]+b4 for i in range(1,n+1)]
    checkpoint('generic_coordinates',original_denominators='generic recurrence denominators; nonzero on the specified exact-order open locus')
    a=[None];bb=[None]
    for i in range(1,n+1):
        inverse=[Q(1)/(X[i]-X[j]) for j in range(1,n+1) if j!=i]
        s1=sum(inverse,Q(0));squares=sum((z*z for z in inverse),Q(0));s2=(s1*s1-squares)/2
        aa=-xp[i]*s1-xpp[i]/(2*xp[i])
        # In a short-origin parameter, x'''/(6*x')=2*x+b2/6.
        # The b2/6 term is independent of i and omitted from every bb_i.
        # In Tate coordinates u_i=b_i-b2/12. Both fixed shifts cancel:
        # bb_i-bb_1 is exactly the local b_i-b_1 and thus u_i-u_1.
        bbi=aa*aa-2*X[i]-xpp[i]*s1-xp[i]*xp[i]*s2
        a.append(aa);bb.append(bbi)
        checkpoint('local_laurent_coefficient',index=i,
                   numerator_degrees=[int(v) for v in bbi.num.degrees()],denominator_degrees=[int(v) for v in bbi.den.degrees()])
        if i>=2:
            entry=cert['g'][str(i)];g=from_rows(entry['num'])
            den=t**entry['den_exp_t']*(t-1)**entry['den_exp_t1']
            assert (bb[i]-bb[1]).equal(Q(g,den)),f'g_{i} differs from direct Laurent coefficient'
            assert (2*(bb[i]-bb[1])).equal(aa*aa-a[1]*a[1]-N*(X[i]-X[1])),f'residue structural identity {i}'
            checkpoint('residue_ratio_identity',index=i,exact_integer_remainder_zero=True)
    receipt.update(status='residue_identities_verified',ratio_identities=n-1,
                   exact_integer_normalizations=Q.normalizations,
                   open_locus_justification='All input coordinate denominators are retained; extra divisions are by2, x_i-x_j and xprime_i. On a smooth odd-order subgroup, distinct pairs have distinct x, and xprime_i=2y_i+a1x_i+a3 is nonzero. Generic polynomial gcd cancellation only cancels factors of these nonzero products. Claimed ratio denominators t and t-1 are original open-locus units.',
                   proof_dependency='Residue theorem identifying ratio differences with local Laurent b_i-b_1, proved in uniform_probe.md',
                   elapsed_seconds=round(time.monotonic()-started,6))
    checkpoint('residue_bridge_verified',ratio_identities=n-1)
    from symbolic_norm_replay import replay
    elimination=replay(certificate_path)
    assert elimination['status']=='passed'
    assert elimination['certificate_sha256']==receipt['certificate_sha256'],'certificate changed during replay'
    assert [row['order'] for row in elimination['orders']]==[N]
    receipt['elimination_and_fibres']=elimination
    receipt['elimination_and_fibres']['remaining_proof_obligation']='discharged by the independently reconstructed local Laurent coefficients and the written residue identity'
    receipt.update(status='passed',elapsed_seconds=round(time.monotonic()-started,6),
                   source_sha256={name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ['flint_replay.py','symbolic_generic.py','symbolic_norm_replay.py','uniform_probe.md']})
    checkpoint('complete_certificate_verified',all_candidate_characteristics_accounted_for=True)
    output.write_text(json.dumps(receipt,indent=2)+'\n');return receipt


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--expected-order',type=int)
    args=parser.parse_args()
    try:verify(args.certificate,args.output,args.expected_order)
    except Exception as exc:
        prior=json.loads(args.output.read_text()) if args.output.exists() else {'schema':'trr07-flint-certificate-replay-v1'}
        prior.update(status='failed',error=repr(exc),
                     certificate_sha256=hashlib.sha256(args.certificate.read_bytes()).hexdigest())
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(prior,indent=2)+'\n')
        raise

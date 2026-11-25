"""Exact affine-polynomial decoder profiles over selected prime fields.

The small curve and modular-basis routines are also used by the exhaustive
residue scan. All arithmetic is integral modulo a prime.
"""
from itertools import product
from math import isqrt
import json
from pathlib import Path
from hashlib import sha256

def prime(n):
    return n>1 and all(n%d for d in range(2,isqrt(n)+1))

class Basis:
    def __init__(self,p): self.p=p; self.rows={}
    def reduce(self,v):
        v=list(v);p=self.p
        for k,w in sorted(self.rows.items()):
            c=v[k]
            if c: v=[(a-c*b)%p for a,b in zip(v,w)]
        return v
    def add(self,v):
        v=self.reduce(v);k=next((i for i,x in enumerate(v) if x),None)
        if k is None:return False
        inv=pow(v[k],-1,self.p);self.rows[k]=[(x*inv)%self.p for x in v];return True
    def contains(self,v):return not any(self.reduce(v))
    def __len__(self):return len(self.rows)

class Curve:
    def __init__(self,p,a,b):
        assert p>3 and (4*a**3+27*b*b)%p
        self.p=p;self.a=a;self.b=b
        sq={}
        for y in range(p):sq.setdefault(y*y%p,[]).append(y)
        self.points=[None]+[(x,y) for x in range(p) for y in sq.get((x*x*x+a*x+b)%p,[])]
    def add(self,P,Q):
        if P is None:return Q
        if Q is None:return P
        p=self.p;x,y=P;u,v=Q
        if x==u and (y+v)%p==0:return None
        slope=((v-y)*pow((u-x)%p,-1,p) if x!=u else (3*x*x+self.a)*pow(2*y,-1,p))%p
        z=(slope*slope-x-u)%p
        return z,(slope*(x-z)-y)%p
    def mat(self,pts,c=0):
        return [[c if (R:=self.add(P,Q)) is None else R[0] for Q in pts] for P in pts]

def probe(C):
    p=C.p;n=len(C.points);pts=C.points[1:];mat=C.mat(pts)
    basis=Basis(p);pole_basis=Basis(p)
    # M symmetric, so columns and rows coincide as vectors indexed by pts.
    rank=Basis(p)
    for v in mat:rank.add(v)
    degree=None;profile=[]
    for d in range(n+2):
        for j in range(d+1):
            i=d-j;basis.add([pow(x,i,p)*pow(y,j,p)%p for x,y in pts])
        ok=all(basis.contains(v) for v in mat)
        profile.append([d,len(basis),ok])
        if ok: degree=d;break
    min_poles=[None]*len(mat)
    for m in range(n+3):
        if m==0:pole_basis.add([1]*len(pts))
        elif m>=2 and m%2==0:pole_basis.add([pow(x,m//2,p) for x,y in pts])
        elif m>=3:pole_basis.add([pow(x,(m-3)//2,p)*y%p for x,y in pts])
        for i,v in enumerate(mat):
            if min_poles[i] is None and pole_basis.contains(v):min_poles[i]=m
        if all(x is not None for x in min_poles):break
    assert 3*degree>=n-4
    return dict(p=p,a=C.a,b=C.b,N=n,rank= len(rank),min_total_degree_per_block=degree,min_poles_hist={str(m):min_poles.count(m) for m in sorted(set(min_poles))},degree_profile=profile)

if __name__=='__main__':
    rows=[]
    for p in [p for p in range(5,80) if prime(p)]:
        seen=set()
        for a,b in product(range(min(p,5)),range(1,min(p,8))):
            if not (4*a**3+27*b*b)%p:continue
            C=Curve(p,a,b);n=len(C.points)
            if not prime(n) or n<7 or n in seen:continue
            seen.add(n);row=probe(C);rows.append(row)
    assert len(rows)==54
    assert all(row['min_total_degree_per_block']==(row['N']+2)//3 for row in rows)
    result=dict(schema='trr03-affine-degree-profiles-v1',
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                counts=dict(curves=len(rows),fields=len(set(row['p'] for row in rows)),
                            full_groups_of_characteristic_order=sum(row['p']==row['N'] for row in rows)),
                profiles=rows)
    Path(__file__).with_name('elliptic_probe_receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result['counts'],sort_keys=True))

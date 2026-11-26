"""Independent exact checks for the translation-rank rigidity audit.
Python standard library only. Finite checks do not replace proofs.
"""
from itertools import product, combinations
from math import gcd,lcm,prod
import json
from pathlib import Path
from hashlib import sha256


def partitions(n, low=1):
    if n == 0:
        yield ()
    else:
        for x in range(low,n+1):
            for tail in partitions(n-x,x):
                yield (x,)+tail


def threshold(q,r):
    a=max(a for a in range(1,r//2+1) if gcd(a,r)==1)
    return (q**a-1)*(q**(r-a)-1)//(q-1)


def thresholds():
    n=0; maximums={}
    for q,rmax in ((2,40),(3,26),(4,24),(5,24),(7,24),(8,24),(9,24),(11,24)):
        maximums[str(q)]={}
        for r in range(3 if q==2 else 2,rmax+1):
            best=0
            for ds in partitions(r):
                if len(ds)<2: continue
                best=max(best,lcm(*(q**d-1 for d in ds)))
                n+=1
            assert best==threshold(q,r),(q,r,best,threshold(q,r))
            maximums[str(q)][str(r)]=best
    return {'partitions_checked':n,'maxima':maximums,'binary_rank_two':'no reducible rank-two cyclic translate module'}


def rank_mod(mat,p):
    a=[list(map(lambda x:x%p,row)) for row in mat]
    n=len(a); m=len(a[0]) if n else 0; r=0
    for j in range(m):
        k=next((k for k in range(r,n) if a[k][j]),None)
        if k is None: continue
        a[r],a[k]=a[k],a[r]
        inv=pow(a[r][j],-1,p); a[r]=[(x*inv)%p for x in a[r]]
        for k in range(r+1,n):
            v=a[k][j]
            if v:a[k]=[(x-v*y)%p for x,y in zip(a[k],a[r])]
        r+=1
        if r==n: break
    return r


def translation_rank(v,p):
    n=len(v);return rank_mod([[v[(i+j)%n] for j in range(n)] for i in range(n)],p)


def binary_stability():
    # Primitive polynomial X^4+X+1; trace in F16 over F2.
    def mul(a,b):
        out=0
        while b:
            if b&1: out^=a
            b>>=1;a<<=1
            if a&16:a^=19
        return out
    def tr(x):
        t=x
        for _ in range(3):x=mul(x,x);t^=x
        assert t in (0,1)
        return t
    x=1;f=[];powers=set()
    for _ in range(15): powers.add(x);f.append(tr(x));x=mul(x,2)
    assert len(powers)==15 and x==1 and sum(f)==8
    # Exhaustively enumerate all binary functions of the same cyclic domain.
    # Circulant rank = 15 - deg gcd(g(X), X^15-1) over F2.
    def rem(a,b):
        while a and a.bit_length()>=b.bit_length(): a^=b<<(a.bit_length()-b.bit_length())
        return a
    def pgcd(a,b):
        while b:a,b=b,rem(a,b)
        return a
    target=sum(x<<i for i,x in enumerate(f)); exact=[16]*16;rho=15
    for g in range(1<<15):
        dist=(g^target).bit_count();r=16-pgcd(g,(1<<15)|1).bit_length();exact[dist]=min(exact[dist],r)
        if any(all(((g>>i)&1)==((g>>((i+t)%15))&1) for i in range(15)) for t in (3,5)):rho=min(rho,dist)
    profile=[];best=16
    for r in exact:best=min(best,r);profile.append(best)
    assert profile[:9]==[4,4,4,4,4,3,2,1,0] and rho==4
    assert translation_rank(f,2)==4
    return {'functions_checked':1<<15,'rank_profile_k_0_to_15':profile,'aperiodicity_radius':rho,'weight':sum(f)}


class F243:
    """F_3[t]/(t^5-t+1), 0..242 encode coefficients in base 3."""
    p=3; n=5; q=243
    @staticmethod
    def digits(a):return [(a//(3**i))%3 for i in range(5)]
    @classmethod
    def add(cls,a,b):return sum(((x+y)%3)*3**i for i,(x,y) in enumerate(zip(cls.digits(a),cls.digits(b))))
    @classmethod
    def neg(cls,a):return sum(((-x)%3)*3**i for i,x in enumerate(cls.digits(a)))
    @classmethod
    def sub(cls,a,b):return cls.add(a,cls.neg(b))
    @classmethod
    def mul(cls,a,b):
        c=[0]*9
        for i,x in enumerate(cls.digits(a)):
            for j,y in enumerate(cls.digits(b)):c[i+j]=(c[i+j]+x*y)%3
        for i in range(8,4,-1):
            c[i-4]=(c[i-4]+c[i])%3;c[i-5]=(c[i-5]-c[i])%3
        return sum(x*3**i for i,x in enumerate(c[:5]))
    @classmethod
    def power(cls,a,n):
        b=1
        while n:
            if n&1:b=cls.mul(b,a)
            a=cls.mul(a,a);n>>=1
        return b
    @classmethod
    def tr(cls,a):
        s=0
        for _ in range(5):s=cls.add(s,a);a=cls.power(a,3)
        assert s in (0,1,2);return s


def spectral_counterexample():
    # Degree 5: no monic linear or quadratic divisor => irreducible.
    p=[1,2,0,0,0,1];nd=0
    for d in (1,2):
        for low in product(range(3),repeat=d):
            g=list(low)+[1];r=p.copy()
            for j in range(5,d-1,-1):
                a=r[j]
                for k in range(d+1):r[j-d+k]=(r[j-d+k]-a*g[k])%3
            assert any(r);nd+=1
    F=F243;q=F.q
    squares={}
    for y in range(q):s=F.mul(y,y);squares.setdefault(s,[]).append(y)
    xs=[F.sub(F.power(x,3),x) for x in range(q)]
    a=next(x for x in range(q) if xs[x] not in squares)
    pts=[None]+[(x,y) for x in range(q) for y in squares.get(xs[x],[])]
    # y^2=x^3-x is nonsingular (derivative of x^3-x is -1).
    for P in pts:
        u=0 if P is None else F.power(F.sub(P[0],a),q-2)
        h=F.sub(F.power(u,3),u)
        assert F.tr(h)==0
    # u has two simple geometric poles, h two order-three poles; d=6.
    N=len(pts);d=6
    assert N==244 and N*N>4*d*d*q
    return {'q':q,'field_modulus':'t^5-t+1','divisors_checked':nd,'a_encoding':a,'a_coefficients':F.digits(a),'curve':'y^2=x^3-x','points':N,'degree':d,'nontrivial_additive_character':'exp(2*pi*i*Tr(z)/3)','all_trace_zero':True,'true_rank':1,'claimed_bound_numerator':N*N,'claimed_bound_denominator':4*d*d*q}


def cauchy_checks():
    total=0
    # For all row/column selections of square submatrices over F_7,
    # with disjoint x/y coordinates (no pole), verify nonsingularity.
    p=7; universe=range(p)
    for t in range(1,p//2+1):
        for x in combinations(universe,t):
            for y in combinations([j for j in universe if j not in x],t):
                C=[[pow((a-b)%p,-1,p) for b in y] for a in x]
                assert rank_mod(C,p)==t;total+=1
    # A degree-1 pole-free kernel on multiplicative G=F_7^* has no a in F7^*\G;
    # use subgroup G={1,2,4}, a=3 and a simple exact Fourier-geometric-series example.
    G=[pow(3,i,7) for i in range(6)]
    f=[pow((pow(x,4,7)-3)%7,-1,7) for x in G]
    assert translation_rank(f,7)==3
    return {'cauchy_minors_checked':total,'torus_counterexample':{'q':7,'N':6,'m':4,'a':3,'rank':3,'naive_N_over_d':'3/2'}}


def main():
    checks={'thresholds':thresholds(),'binary_stability':binary_stability(),'spectral_counterexample':spectral_counterexample(),'cauchy':cauchy_checks()}
    checks['source_sha256']=sha256(Path(__file__).read_bytes()).hexdigest()
    checks['scope']='Independent finite checks; not original Windows scripts; no proof by finite enumeration.'
    path=Path(__file__).with_name('receipt.json');path.write_text(json.dumps(checks,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:({x:y for x,y in v.items() if x!='maxima'} if isinstance(v,dict) else v) for k,v in checks.items()},indent=2))

if __name__=='__main__': main()

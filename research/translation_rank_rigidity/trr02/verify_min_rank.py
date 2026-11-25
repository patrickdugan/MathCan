"""TRR-02: finite exact checks of the cyclic minimum-rank formula.
Standard library only. The written theorem is separate from finite checks.
"""
from functools import lru_cache
from itertools import product
from math import gcd, lcm
from pathlib import Path
import hashlib
import json


def prime_powers(n):
    out=[]; p=2
    while p*p<=n:
        if n%p==0:
            x=1
            while n%p==0:
                x*=p; n//=p
            out.append(x)
        p+=1
    if n>1: out.append(n)
    return out


def order(q,m):
    if m==1: return 1
    assert gcd(q,m)==1
    x=q%m; t=1
    while x!=1:
        x=x*q%m; t+=1
    return t


def split(m,p):
    a=0
    while m%p==0: m//=p; a+=1
    return m,a


def predicted(Q,p,M):
    if M==1: return 1
    m,a=split(M,p); ds=[order(Q,t) for t in prime_powers(m)]
    full=(1<<len(ds))-1
    weight=[1]*(full+1)
    for s in range(1,full+1):
        b=s&-s; weight[s]=lcm(weight[s^b],ds[b.bit_length()-1])
    @lru_cache(None)
    def part(s):
        if s==0: return 0
        b=s&-s; t=s; best=10**100
        while t:
            if t&b: best=min(best,weight[t]+part(s^t))
            t=(t-1)&s
        return best
    if a==0: return part(full)
    e=p**(a-1)+1
    return min(e*weight[s]+part(full^s) for s in range(full+1))


def divisor_dp(Q,p,M):
    # Independent shortest path over divisors, not prime-power partitions.
    if M==1: return 1
    m,a=split(M,p); div=[n for n in range(1,M+1) if M%n==0]
    choices=[]
    for d in div:
        if m%d: continue
        for j in range(a+1):
            e=1 if j==0 else p**(j-1)+1
            choices.append((d*p**j,e*order(Q,d)))
    cost={1:0}
    for x in div:
        if x not in cost: continue
        for d,k in choices:
            z=lcm(x,d)
            if z!=x: cost[z]=min(cost.get(z,10**100),cost[x]+k)
    return cost[M]


def trim(a):
    while a and a[-1]==0: a.pop()
    return a


def rem(a,b,p):
    a=trim(list(a)); inv=pow(b[-1],-1,p)
    while len(a)>=len(b):
        k=len(a)-len(b); t=a[-1]*inv%p
        for j,v in enumerate(b): a[k+j]=(a[k+j]-t*v)%p
        trim(a)
    return a


def cyclic_rank(word,p):
    n=len(word); a=[p-1]+[0]*(n-1)+[1]; b=trim(list(word))
    while b: a,b=b,rem(a,b,p)
    return n-(len(a)-1)


def aperiodic(word,steps):
    n=len(word)
    return all(any(word[i]!=word[(i+t)%n] for i in range(n)) for t in steps)


def main():
    families=((2,2),(3,3),(4,2),(5,5),(7,7),(8,2),(9,3),(11,11),(16,2),(25,5))
    dp_cases=0
    for Q,p in families:
        for M in range(1,161):
            assert predicted(Q,p,M)==divisor_dp(Q,p,M),(Q,p,M)
            dp_cases+=1
    words=0; faithful=0; minima={}
    for p,nmax in ((2,15),(3,9),(5,6)):
        minima[str(p)]={}
        for n in range(1,nmax+1):
            steps=[n//next(j for j in range(2,t+1) if t%j==0) for t in prime_powers(n)]
            best=n+1
            for w in product(range(p),repeat=n):
                words+=1
                if any(w) and aperiodic(w,steps):
                    faithful+=1; best=min(best,cyclic_rank(w,p))
            assert best==predicted(p,p,n),(p,n,best)
            minima[str(p)][str(n)]=best
    # Three-way grouping helps even though all pairwise merges cost more.
    m=9*11*151
    ds=[order(2,t) for t in (9,11,151)]
    assert ds==[6,10,15] and all(lcm(a,b)>a+b for a,b in ((6,10),(6,15),(10,15)))
    assert predicted(2,2,m)==divisor_dp(2,2,m)==30
    out={'schema':'TRR-02/v1','divisor_dp_cases':dp_cases,'words_enumerated':words,
         'nonzero_aperiodic_words':faithful,'minima':minima,
         'triple_example':{'Q':2,'period':m,'orders':ds,'rank':30},
         'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'evidence':'exact finite domain; theorem proved separately'}
    Path(__file__).with_name('receipt.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
    print(json.dumps(out,sort_keys=True))


if __name__=='__main__': main()

"""CTS-09: exact dynamic LP certificate transport (development only)."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'): os.environ[k]='1'
import json,time,random,hashlib,sys
from pathlib import Path
from fractions import Fraction as F
import numpy as np, scipy, sympy
from scipy.optimize._highspy._core import _Highs,HighsStatus,HighsModelStatus,HighsBasisStatus
from scipy.sparse import csr_matrix
from sympy import ZZ
from sympy.polys.matrices import DomainMatrix
ROOT=Path(__file__).resolve().parent
SEED=38009; DIMS=(8,16,32); FAMS=('dense','sparse','correlated','near'); MODES=('affine','general'); STEPS=16; REPS=2; CAP=8
ARMS=('full_direct','full_reuse','previous','direct8','affine8'); LIMIT=2**63-1
KEYS=('hits','calls','iters','tests','dual_reject','primal_reject','scans','rows_scanned','precompute_rows','new','evictions','rhs_updates','fast_mv','big_mv','direct_solves','primal_mat_terms','precompute_mat_terms','seconds')
def dump(name,x): (ROOT/name).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def obj(a): return np.asarray(a,dtype=object)
def dm(a): return DomainMatrix.from_list(np.asarray(a).tolist(),ZZ)
def solve(a,b):
    N,q=dm(a).solve_den(dm(np.asarray(b)[:,None])); q=int(q)
    v=np.array([int(z[0]) for z in N.to_list()],dtype=object)
    return (v if q>0 else -v),abs(q)
def maxabs(a): return max((abs(int(x)) for x in np.asarray(a).flat),default=0)
class SafeMat:
    def __init__(self,a):
        self.o=obj(a);self.m=maxabs(self.o);self.n=self.o.shape[1]
        self.i=self.o.astype(np.int64) if self.m<=LIMIT else None
    def mv(self,v,st):
        m=maxabs(v)
        if self.i is not None and m<=LIMIT and self.n*self.m*m<=LIMIT:
            st['fast_mv']+=1;return self.i@np.asarray(v,dtype=np.int64)
        st['big_mv']+=1;return self.o@obj(v)
def leq(v,b,q):
    if maxabs(b)*q<=LIMIT and q<=LIMIT and np.asarray(v).dtype==np.int64:
        return bool(np.all(v<=np.asarray(b,dtype=np.int64)*q))
    return bool(np.all(obj(v)<=obj(b)*q))
def gen(d,f,s):
    r=np.random.default_rng(s);x=r.integers(-5,6,d);bias=r.integers(-3,4,d)
    if not x.any():x[0]=1
    def normal():
        while True:
            a=r.integers(-5,6,d)
            if f=='sparse':a*=r.random(d)<min(1,4/d)
            if f=='correlated':a+=3*bias
            k=int(a@x)
            if k:return a if k>0 else -a
    while True:
        A=np.stack([normal() for _ in range(d)])
        if np.linalg.matrix_rank(A)==d:break
    rows=list(A);rhs=list(A@x)
    for _ in range(13*d):
        a=normal();rows.append(a);rhs.append(int(a@x)+int(r.integers(1,3) if f=='near' else r.integers(1,31)))
    rows.extend(np.eye(d,dtype=np.int64));rows.extend(-np.eye(d,dtype=np.int64));rhs.extend([8]*2*d)
    A=np.array(rows,dtype=np.int64);b=np.array(rhs,dtype=np.int64);sc=r.integers(1,8,len(b));A*=sc[:,None];b*=sc;c=A[:d].T@r.integers(1,8,d);p=r.permutation(len(b));return A[p],b[p],c

def task(d,f,mode,s):
    A,b0,c=gen(d,f,s);r=np.random.default_rng(s+333333);n=len(b0);mag=max(10,int(np.std(c)));scale=max(1,mag//30)
    anchors=[c]+[r.integers(-mag,mag+1,d) for _ in range(3)]
    B=np.column_stack((A@r.integers(-2,3,d),r.integers(0,4,n),r.integers(0,4,n))).astype(np.int64)
    params=[(0,0,0),(1,2,1),(-1,1,3),(2,3,0),(0,0,0),(1,2,2),(-1,1,3),(2,3,1),(0,1,0),(1,2,1),(-1,0,3),(2,3,0),(0,0,0),(1,1,1),(-1,1,3),(2,3,0)]
    cases=[]
    for t in range(STEPS):
        u=np.array(params[t],dtype=np.int64);cc=anchors[t%4].copy()
        if t%3==2:cc+=r.integers(-scale,scale+1,d)
        if t in (7,13):cc=r.integers(-mag,mag+1,d)
        if not cc.any():cc[0]=1
        if mode=='affine':b=b0+B@u
        else:
            b=b0+B[:,0]*u[0]+r.integers(0,10,n)
            if t==0:b=b0.copy()
        cases.append((b,cc,u))
    assert all(np.all(b-B[:,0]*u[0]>=0) for b,_,u in cases)
    return A,b0,B,cases

def ck(s):
    if s!=HighsStatus.kOk:raise RuntimeError(str(s))
def make(A,b,c):
    h=_Highs();d=len(c);n=len(b)
    for k,v in [('output_flag',False),('solver','simplex'),('simplex_strategy',1),('threads',1),('random_seed',0),('parallel','off')]:ck(h.setOptionValue(k,v))
    ck(h.addCols(d,-c.astype(float),[-np.inf]*d,[np.inf]*d,0,[0]*(d+1),[],[]));mat=csr_matrix(A.astype(float));ck(h.addRows(n,[-np.inf]*n,b.astype(float),mat.nnz,mat.indptr,mat.indices,mat.data));return h

def lp(h,old,A,b,c,st):
    if h is None:h=make(A,b,c);st['rhs_updates']+=len(b)
    else:
        for i in np.flatnonzero(b!=old):ck(h.changeRowBounds(int(i),-np.inf,float(b[i])));st['rhs_updates']+=1
        ck(h.changeColsCost(len(c),np.arange(len(c),dtype=np.int32),-c.astype(float)))
    ck(h.run());assert h.getModelStatus()==HighsModelStatus.kOptimal
    S=np.flatnonzero([q!=HighsBasisStatus.kBasic for q in h.getBasis().row_status]);assert len(S)==len(c),(S,len(c))
    st['calls']+=1;st['iters']+=int(h.getInfo().simplex_iteration_count)
    return h,S

class Entry:
    def __init__(self,A,S,b0,B,affine,st):
        self.S=np.asarray(S,dtype=int);d=len(S);self.key=tuple(map(int,S));self.last=-1
        AS=obj(A.o[self.S]);N,q=dm(AS.T).inv_den();q=int(q);N=obj(N.to_list());self.N=N if q>0 else -N;self.q=abs(q);assert self.q>0 and np.array_equal(AS.T@self.N,self.q*np.eye(d,dtype=np.int64).astype(object))
        self.dual=SafeMat(self.N);self.primal=SafeMat(self.N.T);self.fi=self.N.astype(float)/float(self.q);self.affine=affine
        if affine:
            self.x0=self.N.T@obj(b0[self.S]);T=self.N.T@obj(B[self.S]);self.T=SafeMat(T)
            self.s0=self.q*obj(b0)-A.o@self.x0;self.R=SafeMat(A.o@T-self.q*obj(B));st['precompute_rows']+=len(b0);st['precompute_mat_terms']+=len(b0)*d*(B.shape[1]+1)
            self.s0i=self.s0.astype(np.int64) if maxabs(self.s0)<=LIMIT else None
        st['new']+=1
    def score(self,c):
        y=self.fi@c;return float(np.min(y)/(np.max(np.abs(y))+1e-30))
    def test(self,A,b,c,u,st):
        st['tests']+=1;y=self.dual.mv(c,st)
        if np.any(y<0):st['dual_reject']+=1;return None
        st['scans']+=1;st['rows_scanned']+=len(b)
        if self.affine:
            st['primal_mat_terms']+=len(b)*self.R.n;r=self.R.mv(u,st);s=self.s0i if self.s0i is not None and r.dtype==np.int64 else self.s0
            if not np.all(r<=s):st['primal_reject']+=1;return None
            x=self.x0+obj(self.T.mv(u,st))
        else:
            st['primal_mat_terms']+=len(b)*len(c);x=self.primal.mv(b[self.S],st)
            if not leq(A.mv(x,st),b,self.q):st['primal_reject']+=1;return None
        return str(F(int(obj(c)@obj(x)),self.q))

def direct(A,b,c,S,st):
    x,q=solve(A.o[S],b[S]);y,t=solve(A.o[S].T,c);st['direct_solves']+=2;st['scans']+=1;st['rows_scanned']+=len(b);st['primal_mat_terms']+=len(b)*len(c)
    assert q>0 and t>0 and np.all(y>=0) and leq(A.mv(x,st),b,q) and np.array_equal(A.o[S].T@y,obj(c)*t) and np.array_equal(A.o[S]@x,obj(b[S])*q) and int(obj(c)@x)*t==int(obj(b[S])@y)*q
    return str(F(int(obj(c)@x),q))
def sequence(A0,b0,B,cases,mode,arm):
    setup=time.perf_counter();A=SafeMat(A0);A0.flags.writeable=False;A.o.flags.writeable=False;setup=time.perf_counter()-setup
    h=None;old=None;cache=[];out=[];cap=1 if arm=='previous' else CAP
    for t,(b,c,u) in enumerate(cases):
        ts=time.perf_counter();st={k:0 for k in KEYS};val=None;S=None;entry=None
        affine=arm=='affine8' and mode=='affine'
        if affine:assert np.array_equal(obj(b),obj(b0)+obj(B)@obj(u))
        if arm not in ('full_direct','full_reuse'):
            order=sorted(cache,key=lambda z:(-z.score(c),-z.last,z.key))[:2]
            for e in order:
                val=e.test(A,b,c,u,st)
                if val is not None:entry=e;S=e.S;st['hits']=1;break
        if val is None:
            h,S=lp(h,old,A0,b,c,st);old=b.copy()
            if arm=='full_direct':val=direct(A,b,c,S,st)
            else:
                entry=next((e for e in cache if e.key==tuple(S)),None)
                if entry is None:
                    entry=Entry(A,S,b0,B,affine,st)
                    if len(cache)>=cap:cache.remove(min(cache,key=lambda z:z.last));st['evictions']+=1
                    cache.append(entry)
                val=entry.test(A,b,c,u,st);assert val is not None,(arm,t,S)
        if entry is not None:entry.last=t
        st.update(value=val,support=list(map(int,S)),seconds=time.perf_counter()-ts+(setup if t==0 else 0));out.append(st)
    return out

def summary(rows):return {a:{k:sum(z[k] for r in rows for z in r['arms'][a]) for k in KEYS} for a in ARMS}
def run(repeat=0, start=0,end=12):
    out=[];ts=time.perf_counter()
    for j,f in enumerate(FAMS):
        for ix,d in enumerate(DIMS):
            if not start<=j*len(DIMS)+ix<end:continue
            for m,mode in enumerate(MODES):
                for i in range(REPS):
                    s=SEED+100000*j+1000*d+100*m+i;A,b0,B,cases=task(d,f,mode,s);order=list(ARMS);random.Random(s+repeat*7777).shuffle(order)
                    aa={a:sequence(A,b0,B,cases,mode,a) for a in order};gold=[z['value'] for z in aa['full_direct']];assert all([z['value'] for z in v]==gold for v in aa.values())
                    out.append(dict(seed=s,family=f,dimension=d,mode=mode,arms=aa))
            print('run',repeat,f,d,len(out),round(time.perf_counter()-ts,2),flush=True)
    return out

def stable(rows):return [{**r,'arms':{a:[{k:v for k,v in z.items() if k!='seconds'} for z in vals] for a,vals in r['arms'].items()}} for r in rows]
def summarize(rows):return dict(roots=len(rows),steps=STEPS,arms=len(ARMS),summary=summary(rows),by_mode={m:summary([r for r in rows if r['mode']==m]) for m in MODES},by_dimension={str(d):summary([r for r in rows if r['dimension']==d]) for d in DIMS},by_family={f:summary([r for r in rows if r['family']==f]) for f in FAMS})

def audit(rows):
    checks=neg=cut=norm=overflow=affine_compare=0
    for r in rows:
        A,b0,B,cases=task(r['dimension'],r['family'],r['mode'],r['seed']);AA=SafeMat(A);seen=set()
        for a in ARMS:
            for t,z in enumerate(r['arms'][a]):
                key=(t,tuple(z['support']));b,c,u=cases[t]
                if key in seen:continue
                seen.add(key);st={k:0 for k in KEYS};S=np.array(z['support']);x,q=solve(AA.o[S],b[S]);y,tden=solve(AA.o[S].T,c);assert q>0 and tden>0 and all(y>=0) and all(AA.o@x<=obj(b)*q) and np.array_equal(AA.o[S]@x,obj(b[S])*q) and np.array_equal(AA.o[S].T@y,obj(c)*tden) and int(obj(c)@x)*tden==int(obj(b[S])@y)*q and str(F(int(obj(c)@x),q))==z['value'];checks+=1
        b,c,u=cases[0];S=np.array(r['arms']['full_direct'][0]['support']);st={k:0 for k in KEYS};e=Entry(AA,S,b0,B,r['mode']=='affine',st)
        assert e.test(AA,b,-c,u,st) is None;neg+=1
        j=next(i for i in range(len(b)) if i not in S);x=e.N.T@obj(b[S]);bc=b.copy();bc[j]=int((AA.o[j]@x)//e.q)-1
        ed=Entry(AA,S,b0,B,False,st);assert ed.test(AA,bc,c,u,st) is None;cut+=1
        bad=A[S].copy();bad[0,0]+=1;assert not np.array_equal(obj(bad).T@e.N,e.q*np.eye(len(S),dtype=np.int64).astype(object));norm+=1
        if r['mode']=='affine':
            for b,c,u in cases:
                assert e.test(AA,b,c,u,st)==ed.test(AA,b,c,u,st);affine_compare+=1
    for M,v in [(np.array([[LIMIT,LIMIT]],dtype=object),[2,-2]),(np.array([[LIMIT]],dtype=object),[2]),(np.array([[2]],dtype=object),[-2**63]),(np.array([[LIMIT+1]],dtype=object),[0]),(np.array([[4,5]]),[2,3])]:
        st={k:0 for k in KEYS};assert np.array_equal(obj(SafeMat(M).mv(v,st)),obj(M)@obj(v));overflow+=1
    return dict(independent_certificates=checks,reversed_objective_rejected=neg,inactive_cut_rejected=cut,changed_normal_invalidates_identity=norm,affine_vs_direct_tests=affine_compare,overflow_controls=overflow)

def main():
    dump('protocol.json',dict(schema='CTS-09/dev-v1',seed=SEED,dims=DIMS,families=FAMS,modes=MODES,reps=REPS,steps=STEPS,capacity=CAP,exact_attempt_cap=2,arms=ARMS,primary='affine8 vs full_reuse runtime and exact success; timings descriptive',split='all development',versions=dict(numpy=np.__version__,scipy=scipy.__version__,sympy=sympy.__version__)))
    rows=run();dump('results.json',rows);dump('summary.json',summarize(rows));print('summary',json.dumps(summary(rows)),flush=True)
    a=audit(rows);dump('audit.json',a);print('audit',a,flush=True)
    replay=run(1);assert stable(rows)==stable(replay);dump('replay.json',dict(identical=True,records=len(rows)*STEPS*len(ARMS),**summarize(replay)));print('replay verified',flush=True)
if __name__=='__main__':main()

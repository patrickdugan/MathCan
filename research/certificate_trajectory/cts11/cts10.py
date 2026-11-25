"""CTS-10: lazy affine certificate compilation, exact synthetic development pilot."""
import cts09_reference as ref
import numpy as np
from fractions import Fraction as F
from pathlib import Path
import argparse,json,time,random
ROOT=Path(__file__).resolve().parent
SEED=38010; DIMS=(8,16,32); FAMILIES=('dense','sparse','correlated','near')
MODES=('recurring','mixed'); STEPS=64; CAP=8
ARMS=('full_reuse','direct','eager','lazy')
KEYS=ref.KEYS+('eligible','affine_scans','compile','provenance_terms','compiled_columns','discarded_maps','compiled_scans_on_eviction')
def newstats(): return {k:0 for k in KEYS}
def dump(path,data): Path(path).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
def task(d,f,mode,seed):
    A,b0,c0=ref.gen(d,f,seed); rng=np.random.default_rng(seed+73333); n=len(b0)
    v=rng.integers(-2,3,d,dtype=np.int64)
    side=(A@c0>=0); depth=rng.integers(0,5,n,dtype=np.int64)
    # Synthetic two-sided capacity masks, not actual exchange data.
    B=np.column_stack((A@v,depth*side,depth*(~side))).astype(np.int64)
    mag=max(10,int(np.std(c0))); anchors=[c0]+[rng.integers(-mag,mag+1,d) for _ in range(3)]
    cases=[]
    for t in range(STEPS):
        u=np.array([(t%5)-2,(t//4)%3,((t//4)//3)%3],dtype=np.int64)
        if t%16<12: u[1:]=np.array([(t%4)//2,(t%4)%2])
        c=anchors[t%4].copy()
        if t%16==15:c=rng.integers(-mag,mag+1,d)
        if t%16==10:c+=rng.integers(-max(1,mag//40),max(1,mag//40)+1,d)
        if not c.any():c[0]=1
        b=b0+B@u
        if mode=='mixed' and t%16>=8:b=b+rng.integers(0,12,n,dtype=np.int64)
        assert np.all(b-B[:,0]*u[0]>=0)
        cases.append((b,c,u))
    return A,b0,B,v,cases
class Compiled(ref.Entry):
    def __init__(self,A,S,b0,B,v,st):
        super().__init__(A,S,b0,B,False,st)
        self.eligible=0;self.compiled=False;self.used=0;self.b0=b0;self.B=B;self.v=v
    def compile(self,A,st):
        d=len(self.S);n=len(self.b0)
        x0=self.N.T@ref.obj(self.b0[self.S]);T=self.N.T@ref.obj(self.B[self.S,1:])
        assert np.array_equal(self.N.T@ref.obj(self.B[self.S,0]),self.q*ref.obj(self.v))
        self.s0=self.q*ref.obj(self.b0)-A.o@x0
        self.R=ref.SafeMat(A.o@T-self.q*ref.obj(self.B[:,1:]))
        self.s0i=self.s0.astype(np.int64) if ref.maxabs(self.s0)<=ref.LIMIT else None
        self.compiled=True;st['compile']+=1;st['precompute_rows']+=n
        st['precompute_mat_terms']+=n*d*3;st['compiled_columns']+=2
    def check(self,A,b,c,u,eligible,arm,st):
        st['tests']+=1;y=self.dual.mv(c,st)
        if np.any(y<0):st['dual_reject']+=1;return None
        st['scans']+=1;st['rows_scanned']+=len(b)
        d=len(c);n=len(b);x=None
        if eligible:
            self.eligible+=1;st['eligible']+=1
            if (arm=='eager' or (arm=='lazy' and self.eligible*(d-2)>=3*d)) and not self.compiled:
                self.compile(A,st)
        if eligible and self.compiled:
            self.used+=1;st['affine_scans']+=1;st['primal_mat_terms']+=n*2
            r=self.R.mv(u[1:],st);s=self.s0i if self.s0i is not None and r.dtype==np.int64 else self.s0
            if not np.all(r<=s):st['primal_reject']+=1;return None
        else:
            st['primal_mat_terms']+=n*d;x=self.primal.mv(b[self.S],st)
            if not ref.leq(A.mv(x,st),b,self.q):st['primal_reject']+=1;return None
        if x is None:x=self.primal.mv(b[self.S],st)
        return str(F(int(ref.obj(c)@ref.obj(x)),self.q))
def sequence(A0,b0,B,v,cases,mode,arm):
    start=time.perf_counter();A=ref.SafeMat(A0);A.o.flags.writeable=False;A0.flags.writeable=False
    Bmat=ref.SafeMat(B);assert np.array_equal(A.o@ref.obj(v),ref.obj(B[:,0]));setup=time.perf_counter()-start
    h=None;old=None;cache=[];out=[]
    for t,(b,c,u) in enumerate(cases):
        ts=time.perf_counter();st=newstats();val=None;S=None;entry=None;eligible=False
        if arm in ('eager','lazy'):
            pred=ref.obj(b0)+ref.obj(Bmat.mv(u,st));eligible=np.array_equal(pred,ref.obj(b));st['provenance_terms']+=len(b)*B.shape[1]
        if arm!='full_reuse':
            for e in sorted(cache,key=lambda z:(-z.score(c),-z.last,z.key))[:2]:
                val=e.check(A,b,c,u,eligible,arm,st)
                if val is not None:entry=e;S=e.S;st['hits']=1;break
        if val is None:
            h,S=ref.lp(h,old,A0,b,c,st);old=b.copy()
            entry=next((e for e in cache if e.key==tuple(S)),None)
            if entry is None:
                entry=Compiled(A,S,b0,B,v,st)
                if len(cache)>=CAP:
                    e=min(cache,key=lambda z:z.last);cache.remove(e);st['evictions']+=1
                    if e.compiled:st['discarded_maps']+=1;st['compiled_scans_on_eviction']+=e.used
                cache.append(entry)
            val=entry.check(A,b,c,u,eligible,arm,st);assert val is not None,(arm,t,S)
        entry.last=t
        st.update(value=val,support=list(map(int,S)),seconds=time.perf_counter()-ts+(setup if t==0 else 0));out.append(st)
    return out
def summarize(rows):
    def sums(rs):return {a:{k:sum(x[k] for z in rs for x in z['arms'][a]) for k in KEYS} for a in ARMS}
    return dict(roots=len(rows),steps=STEPS,arms=ARMS,summary=sums(rows),by_mode={m:sums([r for r in rows if r['mode']==m]) for m in MODES},by_dimension={str(d):sums([r for r in rows if r['dimension']==d]) for d in DIMS},by_family={f:sums([r for r in rows if r['family']==f]) for f in FAMILIES})
def run(start,end,rep):
    rows=[];t0=time.perf_counter()
    for j,f in enumerate(FAMILIES):
        for k,d in enumerate(DIMS):
            if not start<=j*len(DIMS)+k<end:continue
            for m,mode in enumerate(MODES):
                seed=SEED+100000*j+1000*d+100*m;A,b0,B,v,cases=task(d,f,mode,seed)
                order=list(ARMS);random.Random(seed+rep*7777).shuffle(order)
                aa={a:sequence(A,b0,B,v,cases,mode,a) for a in order};gold=[z['value'] for z in aa['full_reuse']]
                assert all([z['value'] for z in x]==gold for x in aa.values())
                for a in ('eager','lazy'):
                    assert [(z['value'],z['support'],z['hits'],z['calls'],z['iters']) for z in aa[a]]==[(z['value'],z['support'],z['hits'],z['calls'],z['iters']) for z in aa['direct']]
                rows.append(dict(seed=seed,family=f,dimension=d,mode=mode,arms=aa))
            print('run',rep,f,d,len(rows),round(time.perf_counter()-t0,2),flush=True)
    return rows
def stable(rows):return [{**r,'arms':{a:[{k:v for k,v in z.items() if k!='seconds'} for z in vals] for a,vals in r['arms'].items()}} for r in rows]
def audit(rows):
    counts=dict(independent_certificates=0,affine_direct=0,unstructured_fallback=0,cut_rejected=0,normal_invalidated=0,translation_identity=0,overflow=0,online_bound=0)
    for r in rows:
        A,b0,B,v,cases=task(r['dimension'],r['family'],r['mode'],r['seed']);AA=ref.SafeMat(A);seen=set()
        for arm in ARMS:
            for t,z in enumerate(r['arms'][arm]):
                key=(t,tuple(z['support']))
                if key in seen:continue
                seen.add(key);b,c,u=cases[t];S=np.asarray(z['support']);x,q=ref.solve(AA.o[S],b[S]);y,den=ref.solve(AA.o[S].T,c)
                assert q>0 and den>0 and all(y>=0) and all(AA.o@x<=ref.obj(b)*q) and np.array_equal(AA.o[S]@x,ref.obj(b[S])*q) and np.array_equal(AA.o[S].T@y,ref.obj(c)*den) and int(ref.obj(c)@x)*den==int(ref.obj(b[S])@y)*q and str(F(int(ref.obj(c)@x),q))==z['value']
                counts['independent_certificates']+=1
        S=np.asarray(r['arms']['full_reuse'][0]['support']);st=newstats();e=Compiled(AA,S,b0,B,v,st);e.compile(AA,st);counts['translation_identity']+=1;ed=Compiled(AA,S,b0,B,v,st)
        for b,c,u in cases:
            ok=np.array_equal(ref.obj(b),ref.obj(b0)+ref.obj(B)@ref.obj(u))
            assert e.check(AA,b,c,u,ok,'eager',st)==ed.check(AA,b,c,u,False,'direct',st)
            counts['affine_direct']+=int(ok);counts['unstructured_fallback']+=int(not ok)
        b,c,u=cases[0];x=e.N.T@ref.obj(b[S]);i=next(j for j in range(len(b)) if j not in S);cut=b.copy();cut[i]=int((AA.o[i]@x)//e.q)-1
        assert not np.array_equal(ref.obj(cut),ref.obj(b0)+ref.obj(B)@ref.obj(u));assert e.check(AA,cut,c,u,False,'eager',st) is None;counts['cut_rejected']+=1
        changed=A[S].copy();changed[0,0]+=1;assert not np.array_equal(ref.obj(changed).T@e.N,e.q*np.eye(len(S),dtype=np.int64).astype(object));counts['normal_invalidated']+=1
    for M,v in [(np.array([[ref.LIMIT,ref.LIMIT]],dtype=object),[2,-2]),(np.array([[ref.LIMIT]],dtype=object),[2]),(np.array([[2]],dtype=object),[-2**63]),(np.array([[ref.LIMIT+1]],dtype=object),[0]),(np.array([[4,5]]),[2,3])]:
        assert np.array_equal(ref.obj(ref.SafeMat(M).mv(v,newstats())),ref.obj(M)@ref.obj(v));counts['overflow']+=1
    for d in range(3,65):
        D=d;R=2;C=3*d;k=(C+D-R-1)//(D-R)
        for h in range(257):
            cost=h*D if h<k else (k-1)*D+C+(h-k+1)*R;opt=min(h*D,C+h*R)
            assert opt<=cost<=2*opt;counts['online_bound']+=1
    return counts
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--start',type=int,default=0);p.add_argument('--end',type=int,default=12);p.add_argument('--repeat',type=int,default=0);p.add_argument('--audit-input',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    dump(a.out,audit(json.loads(a.audit_input.read_text())) if a.audit_input else run(a.start,a.end,a.repeat))

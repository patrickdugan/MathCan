"""CTS-13: exact scalar certificates and objective memoization. Serial trusted API."""
from collections import OrderedDict
from dataclasses import dataclass, replace
from fractions import Fraction as F
from pathlib import Path
import argparse, random, time, json
import numpy as np
import cts12 as p
import cts11 as b
import cts09_reference as ref
SEED=38013
ARMS=('full_reuse','vertex','scalar','memo','memo_all')
KEYS=p.KEYS+('objective_terms','coefficient_terms','memo_hits','memo_misses','memo_evictions','vertices','settlements','deferred_vertices','scalar_quotes')
def stats():return dict.fromkeys(KEYS,0)
def objective(c,d):return b.frozen(b.exact_int(c,(d,)))
@dataclass(frozen=True,eq=False,slots=True)
class Receipt:
    revision:str
    generation:int
    objective:bytes
    support:tuple
    value:str
class API(p.SymbolicAPI):
    __slots__=('_receipt','_entry','_vertex')
    def __init__(self,A,b0,B,v):
        super().__init__(A,b0,B,v);self._receipt=self._entry=self._vertex=None
    def issue(self,u,raw):
        s=super().issue(u,raw);self._receipt=self._entry=self._vertex=None;return s
    def quote(self,s,c,e,result,st):
        # Internal trusted call after exact check, not a public attestation interface.
        self.require_current(s,st);e.authorized(self);val,x=result
        self._receipt=Receipt(self.revision,s.generation,c.tobytes(),e.key,val);self._entry=e;self._vertex=x;return self._receipt
    def settle(self,s,c,r,st):
        self.require_current(s,st);c=objective(c,self.A.shape[1])
        if r is None or r is not self._receipt or r.objective!=c.tobytes() or r.generation!=s.generation or r.revision!=self.revision:raise ValueError('invalid receipt')
        e=self._entry;e.authorized(self)
        if self._vertex is None:self._vertex=e.vertex(s.u,st);st['deferred_vertices']+=1
        st['settlements']+=1;return [str(F(int(x),e.q)) for x in self._vertex]
class Entry(p.SymbolicEntry):
    def __init__(self,api,A,S,st):super().__init__(api,A,S,st);self.memo=OrderedDict()
    def compile(self,A,st):super().compile(A,st);self.qv=self.q*ref.obj(self.v)
    def vertex(self,u,st):
        st['vertex_terms']+=3*len(self.S);st['vertices']+=1
        return self.x0+ref.obj(self.T.mv(u[1:],st))+self.qv*int(u[0])
    def value(self,c,u,arm,st):
        key=c.tobytes();coef=self.memo.get(key) if arm.startswith('memo') else None
        if coef is not None:st['memo_hits']+=1;self.memo.move_to_end(key)
        else:
            C=ref.obj(c);coef=(int(C@self.x0),int(C@self.qv),*(int(C@self.T.o[:,j]) for j in range(self.T.n)))
            st['coefficient_terms']+=len(c)*len(coef)
            if arm.startswith('memo'):
                st['memo_misses']+=1;self.memo[key]=coef
                if len(self.memo)>4:self.memo.popitem(last=False);st['memo_evictions']+=1
        st['objective_terms']+=len(u);st['scalar_quotes']+=1
        return str(F(coef[0]+sum(k*int(z) for k,z in zip(coef[1:],u,strict=True)),self.q))
    def check(self,A,api,s,c,arm,st):
        self.authorized(api);eligible=api.require_current(s,st) and arm!='full_reuse'
        st['tests']+=1;y=self.dual.mv(c,st)
        if np.any(y<0):st['dual_reject']+=1;return None
        d=len(c);n=api.n;st['scans']+=1;st['rows_scanned']+=n
        if eligible:
            self.eligible+=1;st['eligible']+=1
            if self.eligible*(d-2)>=3*d and not self.compiled:self.compile(A,st)
        if eligible and self.compiled:
            self.used+=1;st['affine_scans']+=1;st['primal_mat_terms']+=2*n
            u=s.u;r=self.R.mv(u[1:],st);slack=self.s0i if self.s0i is not None and r.dtype==np.int64 else self.s0
            if not np.all(r<=slack):st['primal_reject']+=1;return None
            if arm!='vertex':return self.value(c,u,arm,st),None
            x=self.vertex(u,st)
        else:
            rhs=api.materialize(s,st);st['primal_mat_terms']+=n*d;st['vertex_terms']+=d*d;st['vertices']+=1
            x=self.primal.mv(rhs[self.S],st)
            if not ref.leq(A.mv(x,st),rhs,self.q):st['primal_reject']+=1;return None
        st['objective_terms']+=d;return str(F(int(ref.obj(c)@ref.obj(x)),self.q)),x

def sequence(A0,b0,B,v,cases,arm,settlement):
    ts=time.perf_counter();api=API(A0,b0,B,v);A=ref.SafeMat(api.A);A.o.flags.writeable=False;setup=time.perf_counter()-ts
    h=None;oldb=None;cache=[];out=[]
    for t,(kind,expected,c,u) in enumerate(cases):
        ts=time.perf_counter();st=stats();res=None;e=None;c=objective(c,A0.shape[1]);s=api.factor(u,st) if kind=='factor' else api.raw(expected,st)
        if arm!='full_reuse':
            for e in sorted(cache,key=lambda z:(-z.score(c),-z.last,z.key))[:2]:
                res=e.check(A,api,s,c,arm,st)
                if res is not None:st['hits']=1;break
        if res is None:
            rhs=api.materialize(s,st);h,S=ref.lp(h,oldb,api.A,rhs,c,st);oldb=rhs.copy()
            e=next((z for z in cache if z.key==tuple(S)),None)
            if e is None:
                e=Entry(api,A,S,st)
                if len(cache)>=b.CAP:
                    drop=min(cache,key=lambda z:z.last);cache.remove(drop);st['evictions']+=1
                    if drop.compiled:st['discarded_maps']+=1;st['compiled_scans_on_eviction']+=drop.used
                cache.append(e)
            res=e.check(A,api,s,c,arm,st)
            if res is None:raise RuntimeError('exact certificate rejected')
        receipt=api.quote(s,c,e,res,st);alloc=api.settle(s,c,receipt,st) if t in settlement or arm=='memo_all' else None
        if api._materialized is None:
            assert kind=='factor' and st['hits']==1 and st['affine_scans']>=1;st['symbolic_hits']=1
        e.last=t;st.update(value=res[0],support=list(e.key),allocation=alloc,seconds=time.perf_counter()-ts+(setup if t==0 else 0));out.append(st)
        assert np.array_equal(api.materialize(s,stats()),expected) # fixture outside timing
    return out

def run(start,end,rep):
    rows=[]
    for j,f in enumerate(b.FAMILIES):
        for k,d in enumerate(b.DIMS):
            if not start<=j*len(b.DIMS)+k<end:continue
            for m,mode in enumerate(b.MODES):
                seed=SEED+100000*j+1000*d+100*m;A,b0,B,v,cases=b.task(d,f,mode,seed);order=list(ARMS);random.Random(seed+rep*7777).shuffle(order);settlement=set(random.Random(seed+617).sample(range(len(cases)),len(cases)//4))
                aa={a:sequence(A,b0,B,v,cases,a,settlement) for a in order};gold=[z['value'] for z in aa['full_reuse']]
                assert all([z['value'] for z in x]==gold for x in aa.values())
                for a in ('scalar','memo','memo_all'):
                    assert b.trace(aa[a])==b.trace(aa['vertex'])
                    assert all(aa[a][t]['allocation']==aa['vertex'][t]['allocation'] for t in settlement)
                rows.append(dict(seed=seed,dimension=d,family=f,mode=mode,settlement=sorted(settlement),arms=aa))
            print('finished',rep,f,d,flush=True)
    return rows

def summarize(rows):
    def s(rs):return {a:{k:sum(z[k] for r in rs for z in r['arms'][a]) for k in KEYS} for a in ARMS}
    return dict(roots=len(rows),steps=b.STEPS,summary=s(rows),by_mode={m:s([r for r in rows if r['mode']==m]) for m in b.MODES},by_dim={str(d):s([r for r in rows if r['dimension']==d]) for d in b.DIMS})

def audit(rows):
    count=dict(exact_pairs=0,allocations=0,scalar_identity=0,stale=0,foreign=0,fabricated=0,wrong_objective=0,changed_revision=0,raw_cut=0,big_integer=0,distinct_key=0)
    def reject(fn,key):
        try:fn()
        except ValueError:count[key]+=1
        else:raise AssertionError(key+' accepted')
    for r in rows:
        A,b0,B,v,cases=b.task(r['dimension'],r['family'],r['mode'],r['seed']);AA=ref.obj(A);seen={};api=API(A,b0,B,v);entries={};safe=ref.SafeMat(A)
        for a in ARMS:
            for t,z in enumerate(r['arms'][a]):
                key=(t,tuple(z['support']));kind,rhs,c,u=cases[t];S=np.asarray(z['support'])
                if key not in seen:
                    x,q=ref.solve(AA[S],rhs[S]);y,den=ref.solve(AA[S].T,c)
                    assert q>0 and den>0 and all(y>=0) and all(AA@x<=ref.obj(rhs)*q) and np.array_equal(AA[S]@x,ref.obj(rhs[S])*q) and np.array_equal(AA[S].T@y,ref.obj(c)*den) and int(ref.obj(c)@x)*den==int(ref.obj(rhs[S])@y)*q
                    val=str(F(int(ref.obj(c)@x),q));alloc=[str(F(int(k),q)) for k in x];seen[key]=(val,alloc);count['exact_pairs']+=1
                    if kind=='factor':
                        k=tuple(S)
                        if k not in entries:e=Entry(api,safe,S,stats());e.compile(safe,stats());entries[k]=e
                        e=entries[k];assert e.value(objective(c,len(c)),u,'memo',stats())==val;count['scalar_identity']+=1
                val,alloc=seen[key];assert val==z['value']
                if z['allocation'] is not None:assert alloc==z['allocation'];count['allocations']+=1
        st=stats();kind,rhs,c,u=cases[0];s=api.factor(u,st);c=objective(c,len(c));S=np.asarray(r['arms']['vertex'][0]['support']);e=Entry(api,safe,S,st);e.compile(safe,st)
        result=e.check(safe,api,s,c,'memo',st);assert result is not None;rec=api.quote(s,c,e,result,st);assert api.settle(s,c,rec,st)==seen[(0,tuple(S))][1]
        fake=replace(rec);reject(lambda:api.settle(s,c,fake,st),'fabricated')
        other=API(A,b0,B,v);ss=other.factor(u,st);reject(lambda:other.settle(ss,c,rec,st),'foreign')
        badc=c.copy();badc[0]+=1;reject(lambda:api.settle(s,badc,rec,st),'wrong_objective')
        assert e.value(objective(badc,len(c)),u,'memo',st)==str(F(int(ref.obj(badc)@e.vertex(u,st)),e.q));count['distinct_key']+=1
        cut=rhs.copy();j=next(i for i in range(len(rhs)) if i not in S);xn=e.N.T@ref.obj(rhs[S]);cut[j]=int((AA[j]@xn)//e.q)-1
        raw=api.raw(cut,st);reject(lambda:api.settle(s,c,rec,st),'stale');assert e.check(safe,api,raw,c,'memo',st) is None;count['raw_cut']+=1
        changed=b0.copy();changed[0]+=1;new=API(A,changed,B,v);reject(lambda:e.authorized(new),'changed_revision')
    L=2**40;A=np.eye(2,dtype=np.int64);rhs=np.array([L,L]);B=np.array([[1,0,0],[1,L,0]],dtype=np.int64);v=np.array([1,1]);api=API(A,rhs,B,v);safe=ref.SafeMat(A);e=Entry(api,safe,np.array([0,1]),stats());e.compile(safe,stats());c=objective(np.array([L,L]),2);u=np.array([0,1,0]);assert e.value(c,u,'memo',stats())==str(3*L*L);count['big_integer']+=1
    return count

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--start',type=int,default=0);a.add_argument('--end',type=int,default=12);a.add_argument('--repeat',type=int,default=0);a.add_argument('--audit-input',type=Path);a.add_argument('--out',type=Path,required=True);x=a.parse_args();p.old.dump(x.out,audit(json.loads(x.audit_input.read_text())) if x.audit_input else run(x.start,x.end,x.repeat))

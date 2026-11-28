"""CTS-12: symbolic factor snapshots. Trusted serial API, exact integer arithmetic.
Development benchmark; same LP, cache and routing policy for all cache arms.
"""
import cts11 as prev
import cts10 as old
import cts09_reference as ref
import numpy as np
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import argparse, json, random, time

SEED=38012
ARMS=('full_reuse','direct','eager_rhs','symbolic')
KEYS=prev.KEYS+('rhs_materialized','factor_materialized','symbolic_updates','symbolic_hits','vertex_terms','vertex_compile_terms','envelope_fallback')
ROOT=Path(__file__).resolve().parent

def stats(): return {k:0 for k in KEYS}

@dataclass(frozen=True,eq=False,slots=True)
class Snapshot:
    revision: str
    generation: int
    _u: bytes | None
    _raw: bytes | None
    @property
    def u(self): return None if self._u is None else np.frombuffer(self._u,dtype='<i8')

class SymbolicAPI(prev.FactorAPI):
    __slots__=('_materialized',)
    def __init__(self,A,b0,B,v):
        super().__init__(A,b0,B,v); self._materialized=None
    def issue(self,u,raw):
        self._generation+=1
        self._current=Snapshot(self.revision,self._generation,None if u is None else u.tobytes(),None if raw is None else raw.tobytes())
        self._materialized=raw
        return self._current
    def factor(self,u,st):
        u=prev.exact_int(u,(self.r,)); raw=None
        # Preserve CTS-11's exact solver-input envelope even without RHS construction.
        if self.bound0+self.r*self.boundB*ref.maxabs(u)>prev.SAFE:
            st['envelope_fallback']+=1
            raw=prev.frozen(prev.exact_int(ref.obj(self.b0)+ref.obj(self.B)@ref.obj(u),(self.n,)))
            st['construction_terms']+=self.n*self.r
            st['rhs_materialized']+=1; st['factor_materialized']+=1
        else: st['symbolic_updates']+=1
        st['factor_updates']+=1
        return self.issue(u,raw)
    def raw(self,b,st):
        b=prev.frozen(prev.exact_int(b,(self.n,))); st['raw_updates']+=1; st['rhs_materialized']+=1
        return self.issue(None,b)
    def materialize(self,s,st):
        self.require_current(s,st)
        if self._materialized is None:
            # Cheap bound proved all intermediate products and sums fit int64.
            b=self.b0+self.B@s.u
            self._materialized=prev.frozen(prev.exact_int(b,(self.n,)))
            st['construction_terms']+=self.n*self.r;st['rhs_materialized']+=1;st['factor_materialized']+=1
        return self._materialized.view()

class SymbolicEntry(prev.BoundEntry):
    def compile(self,A,st):
        # Same arithmetic as CTS-11; retain the intermediate affine vertex map.
        d=len(self.S);n=len(self.b0)
        self.x0=self.N.T@ref.obj(self.b0[self.S]);T=self.N.T@ref.obj(self.B[self.S,1:]);self.T=ref.SafeMat(T)
        assert np.array_equal(self.N.T@ref.obj(self.B[self.S,0]),self.q*ref.obj(self.v))
        self.s0=self.q*ref.obj(self.b0)-A.o@self.x0
        self.R=ref.SafeMat(A.o@T-self.q*ref.obj(self.B[:,1:]))
        self.s0i=self.s0.astype(np.int64) if ref.maxabs(self.s0)<=ref.LIMIT else None
        self.compiled=True;st['compile']+=1;st['precompute_rows']+=n
        st['precompute_mat_terms']+=n*d*3;st['compiled_columns']+=2
        st['vertex_compile_terms']+=d*d*4 # x0, two nontranslation columns, translation audit
    def check_snapshot(self,A,api,s,c,arm,st):
        self.authorized(api); eligible=api.require_current(s,st) and arm in ('eager_rhs','symbolic')
        st['tests']+=1;y=self.dual.mv(c,st)
        if np.any(y<0):st['dual_reject']+=1;return None
        d=len(c);n=api.n;st['scans']+=1;st['rows_scanned']+=n
        if eligible:
            self.eligible+=1;st['eligible']+=1
            if self.eligible*(d-2)>=3*d and not self.compiled:self.compile(A,st)
        if eligible and self.compiled:
            self.used+=1;st['affine_scans']+=1;st['primal_mat_terms']+=n*2
            u=s.u; r=self.R.mv(u[1:],st);slack=self.s0i if self.s0i is not None and r.dtype==np.int64 else self.s0
            if not np.all(r<=slack):st['primal_reject']+=1;return None
            if arm=='symbolic':
                x=self.x0+ref.obj(self.T.mv(u[1:],st))+self.q*ref.obj(self.v)*int(u[0]);st['vertex_terms']+=3*d
            else:
                b=api.materialize(s,st);x=self.primal.mv(b[self.S],st);st['vertex_terms']+=d*d
        else:
            b=api.materialize(s,st);st['primal_mat_terms']+=n*d
            x=self.primal.mv(b[self.S],st);st['vertex_terms']+=d*d
            if not ref.leq(A.mv(x,st),b,self.q):st['primal_reject']+=1;return None
        return str(F(int(ref.obj(c)@ref.obj(x)),self.q))

def sequence(A0,b0,B,v,cases,arm):
    t0=time.perf_counter();api=SymbolicAPI(A0,b0,B,v);A=ref.SafeMat(api.A);A.o.flags.writeable=False;setup=time.perf_counter()-t0
    h=None;oldb=None;cache=[];out=[]
    for t,(kind,expected,c,u) in enumerate(cases):
        ts=time.perf_counter();st=stats();val=None;entry=None;S=None
        s=api.factor(u,st) if kind=='factor' else api.raw(expected,st)
        if arm!='symbolic':api.materialize(s,st)
        if arm!='full_reuse':
            for e in sorted(cache,key=lambda z:(-z.score(c),-z.last,z.key))[:2]:
                val=e.check_snapshot(A,api,s,c,arm,st)
                if val is not None:entry=e;S=e.S;st['hits']=1;break
        if val is None:
            b=api.materialize(s,st);h,S=ref.lp(h,oldb,api.A,b,c,st);oldb=b.copy()
            entry=next((e for e in cache if e.key==tuple(S)),None)
            if entry is None:
                entry=SymbolicEntry(api,A,S,st)
                if len(cache)>=prev.CAP:
                    e=min(cache,key=lambda z:z.last);cache.remove(e);st['evictions']+=1
                    if e.compiled:st['discarded_maps']+=1;st['compiled_scans_on_eviction']+=e.used
                cache.append(entry)
            val=entry.check_snapshot(A,api,s,c,arm,st)
            if val is None:raise RuntimeError('certificate rejected')
        if api._materialized is None:
            assert kind=='factor' and arm=='symbolic' and st['hits']==1 and st['affine_scans']>=1
            st['symbolic_hits']=1
        entry.last=t
        st.update(value=val,support=list(map(int,S)),seconds=time.perf_counter()-ts+(setup if t==0 else 0));out.append(st)
        # Fixture check deliberately outside the measured path and counters.
        assert np.array_equal(api.materialize(s,stats()),expected)
    return out

def run(start,end,rep):
    out=[]
    for j,f in enumerate(prev.FAMILIES):
        for k,d in enumerate(prev.DIMS):
            if not start<=j*len(prev.DIMS)+k<end:continue
            for m,mode in enumerate(prev.MODES):
                seed=SEED+100000*j+1000*d+100*m;A,b0,B,v,cases=prev.task(d,f,mode,seed)
                order=list(ARMS);random.Random(seed+rep*7777).shuffle(order)
                aa={a:sequence(A,b0,B,v,cases,a) for a in order};gold=[z['value'] for z in aa['full_reuse']]
                assert all([z['value'] for z in x]==gold for x in aa.values())
                assert all(prev.trace(aa[a])==prev.trace(aa['direct']) for a in ('eager_rhs','symbolic'))
                assert [z['affine_scans'] for z in aa['symbolic']]==[z['affine_scans'] for z in aa['eager_rhs']]
                assert sum(z['symbolic_hits'] for z in aa['symbolic'])==sum(z['factor_materialized'] for z in aa['eager_rhs'])-sum(z['factor_materialized'] for z in aa['symbolic'])
                out.append(dict(seed=seed,dimension=d,family=f,mode=mode,arms=aa))
            print('finished',rep,f,d,flush=True)
    return out

def summarize(rows):
    def s(rs):return {a:{k:sum(z[k] for r in rs for z in r['arms'][a]) for k in KEYS} for a in ARMS}
    return dict(roots=len(rows),steps=prev.STEPS,summary=s(rows),by_mode={m:s([r for r in rows if r['mode']==m]) for m in prev.MODES},by_dim={str(d):s([r for r in rows if r['dimension']==d]) for d in prev.DIMS})

def audit(rows):
    count=dict(exact_pairs=0,symbolic_vertex=0,raw=0,stale=0,foreign=0,fabricated=0,immutable=0,overflow=0,cancellation=0,raw_cut=0,changed_revision=0)
    def reject(fn,exc,key):
        try:fn()
        except exc:count[key]+=1
        else:raise AssertionError(key+' accepted')
    for r in rows:
        A,b0,B,v,cases=prev.task(r['dimension'],r['family'],r['mode'],r['seed']);AA=ref.obj(A);seen=set();api=SymbolicAPI(A,b0,B,v);cache={}
        for a in ARMS:
            for t,z in enumerate(r['arms'][a]):
                key=(t,tuple(z['support']))
                if key in seen:continue
                seen.add(key);kind,b,c,u=cases[t];S=np.asarray(z['support']);x,q=ref.solve(AA[S],b[S]);y,den=ref.solve(AA[S].T,c)
                assert q>0 and den>0 and all(y>=0) and all(AA@x<=ref.obj(b)*q) and np.array_equal(AA[S]@x,ref.obj(b[S])*q) and np.array_equal(AA[S].T@y,ref.obj(c)*den) and int(ref.obj(c)@x)*den==int(ref.obj(b[S])@y)*q and str(F(int(ref.obj(c)@x),q))==z['value'];count['exact_pairs']+=1
                if kind=='factor':
                    k=tuple(S)
                    if k not in cache:
                        e=SymbolicEntry(api,ref.SafeMat(A),S,stats());e.compile(ref.SafeMat(A),stats());cache[k]=e
                    e=cache[k];xn=e.x0+e.T.o@ref.obj(u[1:])+e.q*ref.obj(v)*int(u[0]);assert np.array_equal(xn*q,x*e.q);count['symbolic_vertex']+=1
                else:count['raw']+=1
        st=stats();_,b,c,u=cases[0];s=api.factor(u,st);assert api._materialized is None
        other=SymbolicAPI(A,b0,B,v);foreign=other.factor(u,st)
        reject(lambda:api.materialize(foreign,st),ValueError,'foreign')
        fake=Snapshot(s.revision,s.generation,s._u,s._raw);reject(lambda:api.materialize(fake,st),ValueError,'fabricated')
        reject(lambda:s.u.setflags(write=True),ValueError,'immutable')
        mat=api.materialize(s,st);reject(lambda:mat.setflags(write=True),ValueError,'immutable')
        cut=b.copy();S=np.asarray(r['arms']['full_reuse'][0]['support']);e=SymbolicEntry(api,ref.SafeMat(A),S,st);e.compile(ref.SafeMat(A),st)
        x=e.N.T@ref.obj(b[S]);i=next(j for j in range(len(b)) if j not in S);cut[i]=int((AA[i]@x)//e.q)-1
        raw=api.raw(cut,st);reject(lambda:api.materialize(s,st),ValueError,'stale');assert e.check_snapshot(ref.SafeMat(A),api,raw,c,'symbolic',st) is None;count['raw_cut']+=1
        changed=b0.copy();changed[0]+=1;new=SymbolicAPI(A,changed,B,v);reject(lambda:e.authorized(new),ValueError,'changed_revision')
    A=np.array([[1],[-1]]);Q=prev.SAFE;st=stats();api=SymbolicAPI(A,[1,1],[[1,Q],[-1,Q]],[1]);reject(lambda:api.factor([0,Q],st),OverflowError,'overflow')
    api=SymbolicAPI(A,[1,1],[[1,Q,-Q],[-1,Q,-Q]],[1]);s=api.factor([0,Q,Q],st);assert np.array_equal(api.materialize(s,st),[1,1]);count['cancellation']=1
    return count

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--start',type=int,default=0);p.add_argument('--end',type=int,default=12);p.add_argument('--repeat',type=int,default=0);p.add_argument('--audit-input',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args();old.dump(a.out,audit(json.loads(a.audit_input.read_text())) if a.audit_input else run(a.start,a.end,a.repeat))

"""CTS-11: revision-bound factor construction vs redundant provenance scan.
Synthetic development only; trusted in-process API, not cryptographic authentication.
"""
import cts10 as old
import cts09_reference as ref
import numpy as np
from dataclasses import dataclass
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,random,time

SEED=38011; DIMS=old.DIMS; FAMILIES=old.FAMILIES; MODES=old.MODES; STEPS=64; CAP=8
ARMS=('full_reuse','direct','lazy_checked','lazy_bound')
KEYS=old.KEYS+('factor_updates','raw_updates','construction_terms','authorization_checks','bound_eligible')
SAFE=2**53-1  # exact integer input representation for binary64 HiGHS

def exact_int(a,shape):
    x=np.asarray(a)
    if x.shape!=shape: raise ValueError('shape mismatch')
    if x.dtype.kind not in 'iuO': raise ValueError('integer data required')
    if x.dtype.kind=='O' and any(type(z) is not int and not isinstance(z,np.integer) for z in x.flat): raise ValueError('integer data required')
    if ref.maxabs(x)>SAFE: raise OverflowError('integer exceeds solver input envelope')
    return np.asarray(x,dtype='<i8')

def frozen(a):
    # bytes-backed: callers cannot re-enable the write flag or mutate an input alias.
    a=np.ascontiguousarray(a,dtype='<i8')
    return np.frombuffer(a.tobytes(),dtype='<i8').reshape(a.shape)

@dataclass(frozen=True,eq=False,slots=True)
class Snapshot:
    revision: str
    generation: int
    _b_bytes: bytes
    _u_bytes: bytes | None
    @property
    def b(self):return np.frombuffer(self._b_bytes,dtype="<i8")
    @property
    def u(self):return None if self._u_bytes is None else np.frombuffer(self._u_bytes,dtype="<i8")

class FactorAPI:
    __slots__=("_A","_b0","_B","_v","_revision","_identity","_current","_generation","n","r","bound0","boundB")
    @property
    def A(self):return self._A.view()
    @property
    def b0(self):return self._b0.view()
    @property
    def B(self):return self._B.view()
    @property
    def v(self):return self._v.view()
    @property
    def revision(self):return self._revision
    @property
    def identity(self):return self._identity
    def __init__(self,A,b0,B,v):
        n,d=np.shape(A);r=np.shape(B)[1]
        self._A=frozen(exact_int(A,(n,d))); self._b0=frozen(exact_int(b0,(n,)))
        self._B=frozen(exact_int(B,(n,r))); self._v=frozen(exact_int(v,(d,)))
        if not np.array_equal(ref.obj(self.A)@ref.obj(self.v),ref.obj(self.B[:,0])): raise ValueError('translation factor identity failed')
        h=hashlib.sha256(b'CTS11/revision/v1\0')
        for x in (self.A,self.b0,self.B,self.v):
            h.update(str(x.shape).encode()+b'\0'+x.tobytes())
        self._revision=h.hexdigest();self._identity=object();self._current=None;self._generation=0
        self.n=n;self.r=r;self.bound0=ref.maxabs(self.b0);self.boundB=ref.maxabs(self.B)
    def _issue(self,b,u):
        self._generation+=1
        self._current=Snapshot(self.revision,self._generation,b.tobytes(),None if u is None else u.tobytes())
        return self._current
    def factor(self,u,st):
        u=exact_int(u,(self.r,));st['factor_updates']+=1;st['construction_terms']+=self.n*self.r
        if self.bound0+self.r*self.boundB*ref.maxabs(u)<=SAFE:
            b=self.b0+self.B@u
        else:
            b=ref.obj(self.b0)+ref.obj(self.B)@ref.obj(u)
        return self._issue(exact_int(b,(self.n,)),u)
    def raw(self,b,st):
        b=exact_int(b,(self.n,));st['raw_updates']+=1
        return self._issue(b,None)
    def require_current(self,s,st):
        st['authorization_checks']+=1
        if s is not self._current or s is None or s.revision!=self.revision or s.generation!=self._generation:
            raise ValueError('foreign, stale, or fabricated snapshot')
        return s.u is not None

class BoundEntry(old.Compiled):
    def __init__(self,api,A,S,st):
        self.owner=api.identity;self.revision=api.revision
        super().__init__(A,S,api.b0,api.B,api.v,st)
    def authorized(self,api):
        if self.owner is not api.identity or self.revision!=api.revision:
            raise ValueError('cache revision mismatch')

def task(d,f,mode,seed):
    A,b0,B,v,cases=old.task(d,f,mode,seed)
    # The update source supplies either factors or raw capacities. Do not infer
    # provenance by comparing arrays: the source branch defines its semantics.
    return A,b0,B,v,[(('raw' if mode=='mixed' and t%16>=8 else 'factor'),b,c,u) for t,(b,c,u) in enumerate(cases)]

def sequence(A0,b0,B,v,cases,arm):
    t0=time.perf_counter();api=FactorAPI(A0,b0,B,v);A=ref.SafeMat(api.A);A.o.flags.writeable=False
    Bmat=ref.SafeMat(api.B);setup=time.perf_counter()-t0
    h=None;oldb=None;cache=[];out=[]
    for t,(kind,expected,c,u) in enumerate(cases):
        ts=time.perf_counter();st={k:0 for k in KEYS};val=None;entry=None;S=None
        snap=api.factor(u,st) if kind=='factor' else api.raw(expected,st)
        b=snap.b
        bound=api.require_current(snap,st);eligible=False
        # All policies pay for producing the RHS. Checked arm also performs
        # the legacy second full matrix product (including raw updates).
        if arm=='lazy_checked':
            pred=ref.obj(api.b0)+ref.obj(Bmat.mv(u,st));eligible=np.array_equal(pred,ref.obj(b));st['provenance_terms']+=len(b)*B.shape[1]
        if arm=='lazy_bound':
            eligible=bound;st['bound_eligible']+=int(bound)
        # Never pair a compiled map with a separately supplied factor vector.
        factor_u=snap.u if arm=='lazy_bound' else u
        comp='lazy' if arm.startswith('lazy') else 'direct'
        if arm!='full_reuse':
            for e in sorted(cache,key=lambda z:(-z.score(c),-z.last,z.key))[:2]:
                e.authorized(api);val=e.check(A,b,c,factor_u,eligible,comp,st)
                if val is not None:entry=e;S=e.S;st['hits']=1;break
        if val is None:
            h,S=ref.lp(h,oldb,api.A,b,c,st);oldb=b.copy()
            entry=next((e for e in cache if e.key==tuple(S)),None)
            if entry is None:
                entry=BoundEntry(api,A,S,st)
                if len(cache)>=CAP:
                    e=min(cache,key=lambda z:z.last);cache.remove(e);st['evictions']+=1
                    if e.compiled:st['discarded_maps']+=1;st['compiled_scans_on_eviction']+=e.used
                cache.append(entry)
            entry.authorized(api);val=entry.check(A,b,c,factor_u,eligible,comp,st)
            if val is None:raise RuntimeError('exact certificate rejection on solver candidate')
        entry.last=t
        st.update(value=val,support=list(map(int,S)),seconds=time.perf_counter()-ts+(setup if t==0 else 0));out.append(st)
        # Independent fixture agreement outside timing, not in trusted API path.
        assert np.array_equal(b,expected)
    return out

def stable(rows):return old.stable(rows)
def trace(a):return [(z['value'],z['support'],z['hits'],z['calls'],z['iters']) for z in a]
def run(start,end,rep):
    out=[]
    for j,f in enumerate(FAMILIES):
        for k,d in enumerate(DIMS):
            if not start<=j*len(DIMS)+k<end:continue
            for m,mode in enumerate(MODES):
                seed=SEED+100000*j+1000*d+100*m;A,b0,B,v,cases=task(d,f,mode,seed)
                order=list(ARMS);random.Random(seed+rep*7777).shuffle(order)
                aa={a:sequence(A,b0,B,v,cases,a) for a in order};gold=[z['value'] for z in aa['full_reuse']]
                assert all([z['value'] for z in x]==gold for x in aa.values())
                assert all(trace(aa[a])==trace(aa['direct']) for a in ('lazy_checked','lazy_bound'))
                assert all(x['provenance_terms']==0 for x in aa['lazy_bound'])
                assert [z['affine_scans'] for z in aa['lazy_bound']]==[z['affine_scans'] for z in aa['lazy_checked']]
                out.append(dict(seed=seed,dimension=d,family=f,mode=mode,arms=aa))
            print('finished',rep,f,d,flush=True)
    return out

def summarize(rows):
    def s(rs):return {a:{k:sum(z[k] for r in rs for z in r['arms'][a]) for k in KEYS} for a in ARMS}
    return dict(roots=len(rows),steps=STEPS,summary=s(rows),by_mode={m:s([r for r in rows if r['mode']==m]) for m in MODES},by_dim={str(d):s([r for r in rows if r['dimension']==d]) for d in DIMS})

def audit(rows):
    counts={k:0 for k in ('exact_pairs','factor_constructed','raw_direct','stale','foreign','fabricated','mutated_inputs','immutable_views','revision_changed','same_revision_foreign_cache','raw_cut','wrong_shape','noninteger','overflow','translation_guard','factor_alias','rhs_alias','changed_base_cache','changed_factor_cache','metadata_isolated','raw_matching_still_untrusted')}
    def reject(fn,exc,key):
        try:fn()
        except exc:counts[key]+=1
        else:raise AssertionError(key+' accepted')
    for r in rows:
        A,b0,B,v,cases=task(r['dimension'],r['family'],r['mode'],r['seed']);AA=ref.obj(A); seen=set();st={k:0 for k in KEYS}
        api=FactorAPI(A,b0,B,v);b0copy=b0.copy();Bcopy=B.copy();Acopy=A.copy();other=FactorAPI(Acopy,b0copy,Bcopy,v)
        A0=api.A.copy();Acopy[0,0]+=1;b0copy[0]+=1;Bcopy[0,0]+=1
        assert np.array_equal(other.A,A0) and np.array_equal(other.b0,b0) and np.array_equal(other.B,B);counts['mutated_inputs']+=1
        for a in ARMS:
            for t,z in enumerate(r['arms'][a]):
                key=(t,tuple(z['support']))
                if key in seen:continue
                seen.add(key);kind,b,c,u=cases[t];S=np.asarray(z['support']);x,q=ref.solve(AA[S],b[S]);y,den=ref.solve(AA[S].T,c)
                assert q>0 and den>0 and all(y>=0) and all(AA@x<=ref.obj(b)*q) and np.array_equal(AA[S]@x,ref.obj(b[S])*q) and np.array_equal(AA[S].T@y,ref.obj(c)*den) and int(ref.obj(c)@x)*den==int(ref.obj(b[S])@y)*q and str(F(int(ref.obj(c)@x),q))==z['value'];counts['exact_pairs']+=1
        for kind,b,c,u in cases:
            s=api.factor(u,st) if kind=='factor' else api.raw(b,st)
            assert api.require_current(s,st)==(kind=='factor') and np.array_equal(s.b,b)
            counts['factor_constructed' if kind=='factor' else 'raw_direct']+=1
        s=api.factor(cases[0][3],st);u=s.u.copy();u[0]+=1;s2=api.factor(u,st)
        u[0]+=1;assert s2.u[0]!=u[0];counts['factor_alias']+=1
        tmp=s2.b;tmp.shape=(1,len(tmp));assert s2.b.shape==(len(tmp.ravel()),);counts['metadata_isolated']+=1
        reject(lambda:api.require_current(s,st),ValueError,'stale')
        foreign=other.factor(u,st);reject(lambda:api.require_current(foreign,st),ValueError,'foreign')
        fake=Snapshot(s2.revision,s2.generation,s2.b.tobytes(),s2.u.tobytes());reject(lambda:api.require_current(fake,st),ValueError,'fabricated')
        for x in (api.A,api.b0,api.B,api.v,s2.b,s2.u):reject(lambda x=x:x.setflags(write=True),ValueError,'immutable_views')
        S=np.asarray(r['arms']['full_reuse'][0]['support']);entry=BoundEntry(api,ref.SafeMat(A),S,st)
        reject(lambda:entry.authorized(other),ValueError,'same_revision_foreign_cache')
        # New normals and their translation column, valid revision but stale inverse.
        changed=A.copy();changed[0,0]+=1;newB=B.copy();newB[:,0]=changed@v;new=FactorAPI(changed,b0,newB,v)
        assert new.revision!=api.revision;reject(lambda:entry.authorized(new),ValueError,'revision_changed')
        newb=b0.copy();newb[0]+=1;changedbase=FactorAPI(A,newb,B,v);assert changedbase.revision!=api.revision;reject(lambda:entry.authorized(changedbase),ValueError,'changed_base_cache')
        changedB=B.copy();changedB[0,1]+=1;changedfactor=FactorAPI(A,b0,changedB,v);assert changedfactor.revision!=api.revision;reject(lambda:entry.authorized(changedfactor),ValueError,'changed_factor_cache')
        ss=api.factor(cases[0][3],st);bb=ss.b.copy();raw=api.raw(bb,st);assert not api.require_current(raw,st);counts['raw_matching_still_untrusted']+=1
        bb[0]+=1;assert raw.b[0]!=bb[0];counts['rhs_alias']+=1
        _,b,c,u=cases[0];x=entry.N.T@ref.obj(b[S]);j=next(i for i in range(len(b)) if i not in S);cut=b.copy();cut[j]=int((AA[j]@x)//entry.q)-1
        sc=api.raw(cut,st);assert not api.require_current(sc,st);assert entry.check(ref.SafeMat(A),sc.b,c,u,False,'lazy',st) is None;counts['raw_cut']+=1
        reject(lambda:api.factor([1,2],st),ValueError,'wrong_shape');reject(lambda:api.factor([1.,2.,3.],st),ValueError,'noninteger')
        reject(lambda:api.factor([SAFE+1,0,0],st),OverflowError,'overflow')
        badB=B.copy();badB[0,0]+=1;reject(lambda:FactorAPI(A,b0,badB,v),ValueError,'translation_guard')
    # Overflow of multiplication and addition, even with individually valid inputs.
    A=np.array([[1],[-1]]);B=np.array([[1,SAFE],[-1,SAFE]]);api=FactorAPI(A,[1,1],B,[1]);st={k:0 for k in KEYS}
    reject(lambda:api.factor([0,SAFE],st),OverflowError,'overflow')
    # Large cancelling factors, exact big-int fallback yields small valid RHS.
    B=np.array([[1,SAFE,-SAFE],[-1,SAFE,-SAFE]]);api=FactorAPI(A,[1,1],B,[1]);s=api.factor([0,SAFE,SAFE],st);assert np.array_equal(s.b,[1,1]);counts['overflow_cancellation_exact']=1
    return counts

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--start',type=int,default=0);p.add_argument('--end',type=int,default=12);p.add_argument('--repeat',type=int,default=0);p.add_argument('--audit-input',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args();old.dump(a.out,audit(json.loads(a.audit_input.read_text())) if a.audit_input else run(a.start,a.end,a.repeat))

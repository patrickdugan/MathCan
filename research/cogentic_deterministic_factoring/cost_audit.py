"""DETFACT-13: exact work profiles and certified scheduling."""
import functools, hashlib, json, math, pathlib, random, statistics, sys, time
import numpy as np
from scipy.optimize import nnls
from arena_bench import A, need, run, ref, validate, signature, hash_sig, make
H=pathlib.Path(__file__).resolve().parent
CAPS=[512,768,1024,1536,3072,8192]
SPECS={'train':([1536,6144,12288],[96,192,352],[1,3,6],[64,192,384],9,1301),'test':([2048,8192,16384],[128,256,512],[2,4,8],[96,256,512],12,1302)}
def save(n,o): (H/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
def load(n): return json.loads((H/n).read_text())
def sha(n): return hashlib.sha256((H/n).read_bytes()).hexdigest()
def bc(q): return q.bit_length()+q.bit_count()-2
@functools.lru_cache(maxsize=None)
def primes(k):
    s=bytearray(b'\1')*(k+1);s[:2]=b'\0\0'
    for p in range(2,math.isqrt(k)+1):
        if s[p]:s[p*p:k+1:p]=b'\0'*((k-p*p)//p+1)
    return tuple(p for p in range(3,k+1,2) if s[p])
@functools.lru_cache(maxsize=None)
def profile(k,a):
    S,W=A[a];pp=primes(k);idx=mult=powers=marks=scans=segments=0
    for lo in range(3,k+1,2*S):
        hi=lo+2*(min(S,(k-lo)//2+1)-1);r=math.isqrt(hi);segments+=1;scans+=max(0,(r-1)//2)
        for p in pp:
            if p>r:break
            first=max(p*p,((lo+p-1)//p)*p)
            if first%2==0:first+=p
            if first<=hi:marks+=1+(hi-first)//(2*p)
        chunk=1
        while idx<len(pp) and pp[idx]<=hi:
            p=pp[idx];idx+=1;q=p
            while q<=k//p:q*=p
            if chunk!=1 and chunk.bit_length()+q.bit_length()>W:
                mult+=bc(chunk);powers+=1;chunk=1
            if q.bit_length()>W:mult+=bc(q);powers+=1
            else:chunk*=q
        if chunk!=1:mult+=bc(chunk);powers+=1
    assert idx==len(pp)
    return mult,powers,marks,scans,segments,idx

def features(w,a):
    mult,powers,marks,scans,segments,count=profile(w['k'],a)
    L=(len(w['n'])+7)//8;b=w['batch'];m=int(w['m'],16);u=m>>((m&-m).bit_length()-1)
    mul=b*(bc(u)+mult);calls=b*(1+powers)
    return [1.,mul*L*L/1e6,mul*L/1e5,calls*L/1e4,marks/1e4,scans/1e4,segments/100.,w['k']/1e4,b*L*L/1e3],(mul,calls,count,segments)
def pick(w,c,weights=None):
    ok=[a for a in range(len(A)) if need(w,a)<=c]
    if not ok:return None
    if weights is None:return min(ok,key=lambda a:(need(w,a),-A[a][1],a))
    return min(ok,key=lambda a:(sum(x*y for x,y in zip(features(w,a)[0],weights)),need(w,a),a))
def sweep(ws):
    rows=[];checks=0
    for w in ws:
        v=ref(w);rng=random.Random(w['id']);rr={a:[] for a in range(len(A))}
        for _ in range(3):
            order=list(rr);rng.shuffle(order)
            for a in order:
                r,wall=run(w,a);validate(r,v);_,counts=features(w,a)
                assert counts==tuple(r[k] for k in ('montgomery_multiplications','pow_calls','prime_powers','segments')),(w,a,counts,r)
                rr[a].append((r['seconds'],wall));checks+=w['batch']
        for a,rs in rr.items():rows.append(dict(id=w['id'],action=a,bytes=need(w,a),kernel=[x for x,_ in rs],wall=[y for _,y in rs],median=statistics.median(y for _,y in rs),kernel_median=statistics.median(x for x,_ in rs),features=features(w,a)[0],hash=hash_sig(v)))
        print('grid',w['id'],flush=True)
    return rows,checks

def gmean(x):return math.exp(statistics.mean(map(math.log,x)))
def train():
    sets={k:make(k,v) for k,v in SPECS.items()};save('cost_protocol.json',dict(schema='DETFACT-13-protocol',workloads=sets,actions=A,caps=CAPS,repeats=3,primary='complete every grid-feasible case; abstain on every grid-infeasible case; zero overcap; all exact counters agree',secondary='warm paired end-to-end ratio <=0.99; report cold profile cost separately',model='NNLS on training kernel medians only'))
    rows,checks=sweep(sets['train']);save('cost_train.json',dict(rows=rows,checks=checks))
    weights=nnls(np.asarray([r['features'] for r in rows]),np.asarray([r['kernel_median'] for r in rows]))[0].tolist()
    assert not (H/'cost_test.json').exists()
    d=[dict(id=w['id'],cap=c,minimum=pick(w,c),cost=pick(w,c,weights)) for w in sets['test'] for c in CAPS]
    save('cost_frozen.json',dict(weights=weights,decisions=d,protocol_sha256=sha('cost_protocol.json')));print('frozen',sha('cost_frozen.json'),weights,flush=True)

def test():
    sets=load('cost_protocol.json')['workloads'];assert (H/'cost_frozen.json').exists()
    rows,checks=sweep(sets['test']);save('cost_test.json',dict(rows=rows,checks=checks))

def finish():
    f=load('cost_frozen.json');sets=load('cost_protocol.json')['workloads'];tr=load('cost_train.json');te=load('cost_test.json');lookup={(r['id'],r['action']):r for r in te['rows']};ws={w['id']:w for w in sets['test']};ev=[];calls=0
    rng=random.Random(1303);ds=f['decisions'].copy();rng.shuffle(ds)
    for q in ds:
        w=ws[q['id']];c=q['cap'];ok=[r for r in te['rows'] if r['id']==w['id'] and r['bytes']<=c];best=min(ok,key=lambda r:(r['median'],r['action'])) if ok else None;cold=[]
        for _ in range(3):
            profile.cache_clear();primes.cache_clear();t=time.perf_counter_ns();p=pick(w,c,f['weights']);cold.append((time.perf_counter_ns()-t)/1e9);assert p==q['cost']
        samples={a:[] for a in {q['minimum'],q['cost']} if a is not None}
        for _ in range(3):
            acts=sorted(samples);rng.shuffle(acts)
            for a in acts:
                r,wall=run(w,a,c);calls+=1;assert r['status']=='ok' and hash_sig(signature(r))==lookup[w['id'],a]['hash'];samples[a].append(wall)
        for name in ['minimum','cost']:
            a=q[name];weights=f['weights'] if name=='cost' else None;warm=[]
            for _ in range(31):
                t=time.perf_counter_ns();p=pick(w,c,weights);warm.append((time.perf_counter_ns()-t)/1e9);assert p==a
            inf=statistics.median(warm);coldinf=statistics.median(cold) if name=='cost' else inf;elapsed=statistics.median(samples[a]) if a is not None else None
            ev.append(dict(**q,policy=name,action=a,oracle=best['action'] if best else None,status='ok' if a is not None else 'preflight_unresolved',allocated=need(w,a) if a is not None else 0,warm_inference=inf,cold_inference=coldinf,capped_wall=samples.get(a),warm_total=elapsed+inf if elapsed is not None else None,cold_total=elapsed+coldinf if elapsed is not None else None,grid_regret=(lookup[w['id'],a]['median']+inf)/best['median'] if a is not None else None))
    summary={}
    for name in ['minimum','cost']:
        rr=[r for r in ev if r['policy']==name];feas=[r for r in rr if r['oracle'] is not None];good=[r for r in feas if r['status']=='ok'];summary[name]=dict(feasible=len(feas),completed=len(good),preflight_abstentions=sum(r['status']=='preflight_unresolved' for r in rr),overcap=sum(r['allocated']>r['cap'] for r in rr),grid_best_hits=sum(r['action']==r['oracle'] for r in good),geomean_grid_regret=gmean([r['grid_regret'] for r in good]),median_warm_us=statistics.median(r['warm_inference'] for r in rr)*1e6,median_cold_us=statistics.median(r['cold_inference'] for r in rr)*1e6)
    pairs={}
    for r in ev:pairs.setdefault((r['id'],r['cap']),{})[r['policy']]=r
    good=[p for p in pairs.values() if p['cost']['status']==p['minimum']['status']=='ok'];warm=gmean([p['cost']['warm_total']/p['minimum']['warm_total'] for p in good]);cold=gmean([p['cost']['cold_total']/p['minimum']['cold_total'] for p in good]);group={}
    for p in good:group.setdefault(p['cost']['id'],[]).append(math.log(p['cost']['warm_total']/p['minimum']['warm_total']))
    keys=sorted(group);br=random.Random(1304);boot=[]
    for _ in range(3000):boot.append(math.exp(statistics.mean(v for _ in keys for v in group[br.choice(keys)])))
    boot.sort();primary=all(r['completed']==r['feasible'] and r['preflight_abstentions']==len(ds)-r['feasible'] and r['overcap']==0 for r in summary.values())
    receipt=dict(schema='DETFACT-13',protocol_sha256=sha('cost_protocol.json'),frozen_sha256=sha('cost_frozen.json'),grid_runs=sum(map(len,sets.values()))*len(A)*3,arithmetic_checks=tr['checks']+te['checks'],exact_counter_checks=sum(map(len,sets.values()))*len(A)*3,capped_runs=calls,summary=summary,paired=dict(cases=len(good),workloads=len(group),switches=sum(p['cost']['action']!=p['minimum']['action'] for p in good),warm_ratio=warm,cold_ratio=cold,bootstrap95=[boot[75],boot[2925]],speed_gate=warm<=.99),primary_pass=primary,weights=f['weights'],evaluations=ev)
    save('cost_receipt.json',receipt);print(json.dumps({k:v for k,v in receipt.items() if k!='evaluations'},indent=2),flush=True)
if __name__=='__main__':{'train':train,'test':test,'finish':finish}[sys.argv[1]]()

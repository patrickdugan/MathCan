"""DETFACT-14: prospective static vs frozen structural scheduling."""
import json, hashlib, math, pathlib, random, statistics, subprocess, sys, time
from collections import Counter
from arena_bench import A, need, run, ref, validate, make, hash_sig
from cost_audit import features, pick, profile, primes
H=pathlib.Path(__file__).resolve().parent
CAPS=[512,768,1024,1536,3072,8192]
SPEC=([24576,40960,65536],[160,384,640],[2,5,10],[128,384,896],12,1402)

def save(n,o): (H/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
def load(n): return json.loads((H/n).read_text())
def sha(n): return hashlib.sha256((H/n).read_bytes()).hexdigest()
def gmean(xs): return math.exp(statistics.mean(map(math.log,xs)))
def static(w,c): return 0 if need(w,0)<=c else None

def choose(name,w,c,weights):
    if name=='static16':return static(w,c)
    if name=='minimum':return pick(w,c)
    return pick(w,c,weights)

def freeze():
    assert not (H/'static_receipt.json').exists()
    subprocess.run(['gcc','-O3','-std=c11','-Wall','-Wextra','-Werror','-Wvla',str(H/'arena_audit.c'),'-o',str(H/'arena_audit')],check=True)
    prev=load('cost_frozen.json');weights=prev['weights'];ws=make('test',SPEC)
    protocol=dict(schema='DETFACT-14-protocol',workloads=ws,actions=A,caps=CAPS,repeats=3,prior_weights_sha256=sha('cost_frozen.json'),primary='all policies complete all grid-feasible cases; abstain when infeasible; exact arithmetic and counter agreement; zero overcap',speed='static16 vs certified minimum: paired geometric mean warm dispatch ratio <=0.99 and report workload bootstrap interval; compare cached cost, cold first decision and kernel separately',timing='randomized grid repeats under exact per-action arena cap; shared action timings across policies and caps; measure selector separately, no per-policy rerun; workload-clustered bootstrap',seed=1403)
    save('static_protocol.json',protocol)
    ds=[]
    for w in ws:
        for c in CAPS:
            d={n:choose(n,w,c,weights) for n in ('minimum','static16','cost')}
            ds.append(dict(id=w['id'],cap=c,choices=d))
    save('static_frozen.json',dict(protocol_sha256=sha('static_protocol.json'),weights=weights,decisions=ds))
    print('frozen',sha('static_frozen.json'),Counter(q['choices']['cost'] for q in ds),flush=True)

def measure(start,end):
    p=load('static_protocol.json');f=load('static_frozen.json');assert f['protocol_sha256']==sha('static_protocol.json')
    for w in p['workloads'][start:end]:
        expected=ref(w);rng=random.Random('DETFACT14:'+w['id']);rows={a:[] for a in range(len(A))};bounds=0
        for _ in range(p['repeats']):
            order=list(rows);rng.shuffle(order)
            for a in order:
                cap=need(w,a);r,wall=run(w,a,cap);validate(r,expected)
                _,counts=features(w,a);assert counts==tuple(r[k] for k in ('montgomery_multiplications','pow_calls','prime_powers','segments'))
                rows[a].append(dict(wall=wall,kernel=r['seconds'],allocated=r['allocated_bytes'],counters=list(counts)))
        for a in rows:
            r,_=run(w,a,need(w,a)-1);assert r['status']=='unresolved' and r['allocated_bytes']==0;bounds+=1
        save('static_'+w['id']+'.json',dict(id=w['id'],hash=hash_sig(expected),rows=[dict(action=a,arena=need(w,a),runs=rs) for a,rs in rows.items()],boundary_rejections=bounds))
        print('measured',w['id'],flush=True)

def finish():
    p=load('static_protocol.json');f=load('static_frozen.json');ws={w['id']:w for w in p['workloads']};weights=f['weights'];grid=[load('static_'+i+'.json') for i in ws];lookup={(r['id'],v['action']):v for r in grid for v in r['rows']};ev=[]
    for q in f['decisions']:
        w=ws[q['id']];c=q['cap'];ok=[a for a in range(len(A)) if need(w,a)<=c]
        def med(a,k):return statistics.median(v[k] for v in lookup[w['id'],a]['runs'])
        oracle=min(ok,key=lambda a:(med(a,'wall'),a)) if ok else None
        cold=[]
        for _ in range(3):
            profile.cache_clear();primes.cache_clear();t=time.perf_counter_ns();a=choose('cost',w,c,weights);cold.append((time.perf_counter_ns()-t)/1e9);assert a==q['choices']['cost']
        for name,a in q['choices'].items():
            assert (a is None)==(not ok)
            times=[]
            for _ in range(31):
                t=time.perf_counter_ns();r=choose(name,w,c,weights);times.append((time.perf_counter_ns()-t)/1e9);assert r==a
            inf=statistics.median(times);cinf=statistics.median(cold) if name=='cost' else inf
            alloc=need(w,a) if a is not None else 0;assert alloc<=c
            ev.append(dict(id=w['id'],cap=c,policy=name,action=a,oracle=oracle,allocated=alloc,warm_inference=inf,cold_inference=cinf,warm_total=med(a,'wall')+inf if a is not None else None,cold_total=med(a,'wall')+cinf if a is not None else None,kernel=med(a,'kernel') if a is not None else None,regret=(med(a,'wall')+inf)/med(oracle,'wall') if a is not None else None))
    summary={};pairs={}
    for r in ev:pairs.setdefault((r['id'],r['cap']),{})[r['policy']]=r
    for n in ('minimum','static16','cost'):
        rr=[r for r in ev if r['policy']==n];good=[r for r in rr if r['action'] is not None]
        summary[n]=dict(completed=len(good),abstained=len(rr)-len(good),overcap=sum(r['allocated']>r['cap'] for r in rr),grid_best_hits=sum(r['oracle']==r['action'] for r in good),gmean_regret=gmean([r['regret'] for r in good]),warm_us=statistics.median(r['warm_inference'] for r in rr)*1e6,cold_us=statistics.median(r['cold_inference'] for r in rr)*1e6,actions=dict(Counter(str(r['action']) for r in rr)))
    ratios={}
    for n in ('static16','cost'):
        joint=[p for p in pairs.values() if p[n]['action'] is not None];group={}
        for p in joint:group.setdefault(p[n]['id'],[]).append(math.log(p[n]['warm_total']/p['minimum']['warm_total']))
        rng=random.Random(1404);keys=sorted(group);boot=sorted(math.exp(statistics.mean(v for _ in keys for v in group[rng.choice(keys)])) for _ in range(3000))
        ratios[n]=dict(warm=gmean([p[n]['warm_total']/p['minimum']['warm_total'] for p in joint]),cold=gmean([p[n]['cold_total']/p['minimum']['cold_total'] for p in joint]),kernel=gmean([p[n]['kernel']/p['minimum']['kernel'] for p in joint]),bootstrap95=[boot[75],boot[2925]],switches=sum(p[n]['action']!=p['minimum']['action'] for p in joint),cases=len(joint),workloads=len(keys))
    joint=[p for p in pairs.values() if p['static16']['action'] is not None]
    compare=dict(same_action=sum(p['static16']['action']==p['cost']['action'] for p in joint),static_to_cost_warm=gmean([p['static16']['warm_total']/p['cost']['warm_total'] for p in joint]),static_to_cost_cold=gmean([p['static16']['cold_total']/p['cost']['cold_total'] for p in joint]))
    count=len(A)*load('static_protocol.json')['repeats'];receipt=dict(schema='DETFACT-14',protocol_sha256=sha('static_protocol.json'),frozen_sha256=sha('static_frozen.json'),grid_runs=len(ws)*count,arithmetic_checks=sum(w['batch'] for w in ws.values())*count,counter_checks=len(ws)*count,boundary_rejections=sum(r['boundary_rejections'] for r in grid),summary=summary,ratios=ratios,static_vs_cost=compare,feasibility_pass=all(r['overcap']==0 for r in summary.values()),speed_gate=ratios['static16']['warm']<=.99,grid=grid,evaluations=ev)
    save('static_receipt.json',receipt);print(json.dumps({k:v for k,v in receipt.items() if k not in ('grid','evaluations')},indent=2),flush=True)

if __name__=='__main__':
    phase=sys.argv[1]
    if phase=='freeze':freeze()
    elif phase=='measure':measure(int(sys.argv[2]),int(sys.argv[3]))
    elif phase=='finish':finish()

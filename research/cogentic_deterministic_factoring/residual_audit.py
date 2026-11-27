"""DETFACT-11: residual scheduling for synthetic modular execution; replay by phase."""
import hashlib,json,math,pathlib,random,statistics,subprocess,time,sys
from collections import defaultdict,Counter
from itertools import product
from sklearn.linear_model import Ridge
from policy_audit import A,CAPS,ref,sig,fixed
H=pathlib.Path(__file__).resolve().parent
SPECS={'train':([8192,32768,98304],[72,144,256],[1,4,8],[48,128,320],12,511),'cal':([12288,49152,114688],[88,176,320],[3,6,10],[64,192,448],6,512),'test':([24576,81920,147456],[112,224,448],[2,7,16],[96,256,768],12,513)}
def save(f,o): (H/f).write_text(json.dumps(o,indent=2)+'\n')
def load(f):return json.loads((H/f).read_text())
def sha(f):return hashlib.sha256((H/f).read_bytes()).hexdigest()
def make(split,spec):
    ks,ns,bs,ms,count,seed=spec;rng=random.Random(seed);levels=[];out=[]
    for seq in (ks,ns,bs,ms):
        x=(seq*((count+2)//3))[:count];rng.shuffle(x);levels.append(x)
    def odd(b):return rng.getrandbits(b-1)|(1<<(b-1))|1
    for i,(k,n,b,m) in enumerate(zip(*levels)):
        a=n//3 if split=='test' and i%2 else n//2
        N=odd(a)*odd(n-a);M=odd(m-3)<<3
        out.append(dict(id=f'{split}-{i:02}',split=split,k=k,n=str(N),m=str(M),nbits=N.bit_length(),target_nbits=n,mbits=M.bit_length(),batch=b))
    assert all(set(w[key] for w in out)==set(values) for key,values in [('k',ks),('target_nbits',ns),('batch',bs),('mbits',ms)])
    return out

def call(w,a,cap=0):
    mode,s,c=A[a];t=time.perf_counter_ns();p=subprocess.run([str(H/'native_audit'),mode,*map(str,[w['k'],s,c,w['batch'],cap,w['n'],w['m']])],capture_output=True,text=True)
    if p.returncode==3:
        assert 'workspace budget exhausted' in p.stderr;return None,(time.perf_counter_ns()-t)/1e9
    if p.returncode:raise RuntimeError(p.stderr)
    r=json.loads(p.stdout);assert r['live_after_clear_bytes']==0
    return r,(time.perf_counter_ns()-t)/1e9

def measure(w):
    expected=ref(w);sample=defaultdict(list);rng=random.Random(w['id'])
    for _ in range(3):
        order=list(range(len(A)));rng.shuffle(order)
        for a in order:
            r,wall=call(w,a);assert sig(r)==expected;sample[a].append((r,wall))
    rows=[]
    for a,v in sorted(sample.items()):
        rs=[r for r,_ in v];wall=[s for _,s in v];rows.append(dict(id=w['id'],action=a,seconds=[r['seconds'] for r in rs],median=statistics.median(r['seconds'] for r in rs),wall=wall,wall_median=statistics.median(wall),payload=max(r['peak_payload_full_run_bytes'] for r in rs),hash=expected))
    save(w['id']+'.json',rows);print('measured',w['id'],w['k'],w['batch'],flush=True)
def features(w):return [math.log2(w[k]) for k in ('k','nbits','batch','mbits')]
def pred(m,x):return m['intercept']+sum(a*b for a,b in zip(m['coef'],x))
def fit(train,cal,ws):
    tr={(r['id'],r['action']):r for r in train};ca={(r['id'],r['action']):r for r in cal};ti=sorted({r['id'] for r in train});ci=sorted({r['id'] for r in cal})
    def one(y):
        m=Ridge(alpha=1.).fit([features(ws[i]) for i in ti],[y(tr,i) for i in ti]);return dict(coef=m.coef_.tolist(),intercept=float(m.intercept_))
    mem=[];delta={}
    for a in range(len(A)):
        y=lambda d,i:math.log(d[i,a]['payload']);m=one(y);m['margin']=max(0.,max(y(ca,i)-pred(m,features(ws[i])) for i in ci))+math.log(1.05);mem.append(m)
    for b,a in product(range(len(A)),repeat=2):
        if a==b:continue
        y=lambda d,i:math.log(d[i,b]['wall_median']/d[i,a]['wall_median']);m=one(y);m['margin']=max(0.,max(pred(m,features(ws[i]))-y(ca,i) for i in ci));delta[f'{b}:{a}']=m
    return mem,delta

def pick(w,cap,baseline,mem,delta):
    b=baseline[str(cap)];x=features(w);upper=[pred(m,x)+m['margin'] for m in mem];ok=[a for a,u in enumerate(upper) if u<=math.log(cap)]
    if b not in ok:
        if not ok:return min(range(len(A)),key=lambda a:(upper[a],a)),'predicted_no_feasible'
        return min(ok,key=lambda a:(upper[a],a)),'memory_rescue'
    candidates=[]
    for a in ok:
        if a==b:continue
        d=delta[f'{b}:{a}'];lower=pred(d,x)-d['margin']
        if lower>math.log(1.02):candidates.append((lower,-a))
    if not candidates:return b,'abstain'
    return -max(candidates)[1],'predicted_speed_gain'

def allrows(sets,split):return [r for w in sets[split] for r in load(w['id']+'.json')]
def init():
    subprocess.run(['gcc','-O3','-std=c11','-Wall','-Wextra','-Werror',str(H/'native_audit.c'),'-lgmp','-o',str(H/'native_audit')],check=True)
    sets={k:make(k,v) for k,v in SPECS.items()}
    save('protocol.json',dict(schema='DETFACT-11-protocol',specs=SPECS,actions=A,caps=CAPS,repeats=3,primary='no extra avoidable budget failures and paired gmean actual capped wall ratio residual/fixed <=0.99; descriptive, workload bootstrap',gate='lower calibrated pairwise log wall gain > log(1.02); rescue if baseline predicted over budget; no retries',memory='ridge log payload + max positive calibration residual + log(1.05)',seed=514,workloads=sets))
    print('protocol',sha('protocol.json'),flush=True)
def freeze(sets,ws):
    assert not any((H/(w['id']+'.json')).exists() for w in sets['test'])
    train=allrows(sets,'train');cal=allrows(sets,'cal');base={str(c):fixed([{**r,'median':r['wall_median']} for r in train],c) for c in CAPS};mem,delta=fit(train,cal,ws)
    f=dict(fixed=base,mem=mem,delta=delta,decisions=[])
    for w in sets['test']:
        for c in CAPS:
            a,reason=pick(w,c,base,mem,delta);f['decisions'].append(dict(id=w['id'],cap=c,fixed=base[str(c)],residual=a,reason=reason))
    save('frozen_residual.json',f);print('frozen',sha('frozen_residual.json'),base,Counter(q['reason'] for q in f['decisions']),flush=True)

def capped(sets,ws,start,end):
    f=load('frozen_residual.json');base,mem,delta=(f[k] for k in ('fixed','mem','delta'));test=allrows(sets,'test');lookup={(r['id'],r['action']):r for r in test};rng=random.Random(514);decisions=f['decisions'].copy();rng.shuffle(decisions)
    for j,q in enumerate(decisions[start:end],start):
        w=ws[q['id']];c=q['cap'];feas=[r for r in test if r['id']==w['id'] and r['payload']<=c];best=min(feas,key=lambda r:(r['wall_median'],r['action'])) if feas else None;measured={};rr=[];local_rng=random.Random(514+j)
        for _ in range(3):
            acts=sorted({q['fixed'],q['residual']});local_rng.shuffle(acts)
            for a in acts:
                r,wall=call(w,a,c);expected=lookup[w['id'],a];assert (r is not None)==(expected['payload']<=c)
                if r is not None:assert r['peak_payload_full_run_bytes']<=c and sig(r)==expected['hash']
                measured.setdefault(a,[]).append(dict(ok=r is not None,wall=wall,payload=r['peak_payload_full_run_bytes'] if r else None))
        for name in ['fixed','residual']:
            a=q[name];inf=[]
            for _ in range(31):
                t=time.perf_counter_ns();p=base[str(c)] if name=='fixed' else pick(w,c,base,mem,delta)[0];inf.append((time.perf_counter_ns()-t)/1e9);assert p==a
            v=measured[a];i=statistics.median(inf);ok=v[0]['ok'];assert all(x['ok']==ok for x in v)
            rr.append(dict(**q,policy=name,action=a,oracle=best['action'] if best else None,status='ok' if ok else 'budget',inference=i,inference_runs=inf,capped_wall_runs=v,capped_total=statistics.median(x['wall'] for x in v)+i,grid_regret=(lookup[w['id'],a]['wall_median']+i)/best['wall_median'] if best and ok else None))
        save(f'cap-{j:03}.json',rr)
    print('capped',start,end,flush=True)

def gmean(xs):return math.exp(statistics.mean(map(math.log,xs))) if xs else None

def finish(sets):
    f=load('frozen_residual.json');rows=[r for j in range(len(f['decisions'])) for r in load(f'cap-{j:03}.json')];summary={}
    for name in ['fixed','residual']:
        r=[x for x in rows if x['policy']==name];ok=[x for x in r if x['oracle'] is not None and x['status']=='ok'];reg=[x['grid_regret'] for x in ok]
        summary[name]=dict(feasible=sum(x['oracle'] is not None for x in r),completed=len(ok),avoidable_aborts=sum(x['oracle'] is not None and x['status']!='ok' for x in r),unavoidable_aborts=sum(x['oracle'] is None and x['status']!='ok' for x in r),geomean_grid_regret=gmean(reg),max_grid_regret=max(reg) if reg else None,median_inference_us=statistics.median(x['inference'] for x in r)*1e6)
    pairs=defaultdict(dict)
    for r in rows:pairs[r['id'],r['cap']][r['policy']]=r
    group=defaultdict(list);switch=defaultdict(int);wins=ties=losses=0
    for (i,c),p in pairs.items():
        b,l=p['fixed'],p['residual'];switch[l['reason']]+=1
        if b['status']==l['status']=='ok':
            ratio=l['capped_total']/b['capped_total'];group[i].append(math.log(ratio));wins+=ratio<1;ties+=ratio==1;losses+=ratio>1
    vals=[v for vs in group.values() for v in vs];ratio=math.exp(statistics.mean(vals));rng=random.Random(515);keys=sorted(group);boots=[]
    for _ in range(3000):
        z=[v for _ in keys for v in group[rng.choice(keys)]];boots.append(math.exp(statistics.mean(z)))
    boots.sort();paired=dict(cases=len(vals),workloads=len(keys),gmean_ratio=ratio,bootstrap95=[boots[75],boots[2925]],wins=wins,ties=ties,losses=losses,reasons=dict(switch),actual_switches=sum(q['fixed']!=q['residual'] for q in f['decisions']),primary_pass=summary['residual']['avoidable_aborts']<=summary['fixed']['avoidable_aborts'] and ratio<=.99)
    count=sum(w['batch'] for v in sets.values() for w in v);result=dict(schema='DETFACT-11',protocol_sha256=sha('protocol.json'),frozen_sha256=sha('frozen_residual.json'),workloads=sets,train=allrows(sets,'train'),calibration=allrows(sets,'cal'),test=allrows(sets,'test'),checks=count*len(A)*3,grid_runs=sum(map(len,sets.values()))*len(A)*3,capped_runs=sum(3*len({q['fixed'],q['residual']}) for q in f['decisions']),summary=summary,paired=paired,evaluations=rows)
    save('residual_receipt.json',result);print(json.dumps({k:result[k] for k in ['checks','grid_runs','capped_runs','summary','paired']},indent=2),flush=True)
if __name__=='__main__':
    phase=sys.argv[1]
    if phase=='init':init()
    else:
        sets=load('protocol.json')['workloads'];ws={w['id']:w for v in sets.values() for w in v}
        if phase in sets:
            if phase=='test':assert (H/'frozen_residual.json').exists()
            for w in sets[phase][int(sys.argv[2]):int(sys.argv[3])]:measure(w)
        elif phase=='freeze':freeze(sets,ws)
        elif phase=='capped':capped(sets,ws,int(sys.argv[2]),int(sys.argv[3]))
        elif phase=='finish':finish(sets)
